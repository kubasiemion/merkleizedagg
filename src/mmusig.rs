use bitcoin::hashes::hash160::Hash;
use schnorr_fun::binonce::{Nonce, NonceKeyPair};
use schnorr_fun::{adaptor::EncryptedSignature, Message, Schnorr, Signature};
use secp256kfun::{
    digest::{generic_array::typenum::U32, Digest},
    g,
    hash::{HashAdd, Tag},
    marker::*,
    nonce::{self, NoNonces, NonceGen},
    op,
    rand_core::{RngCore, SeedableRng},
    s, KeyPair, Point, Scalar, G,
};
use std::collections::HashMap;
// The MuSig context.
pub struct MuSig<H, NG> {
    /// The hash used to compress the key list to 32 bytes.
    pk_hash: H,
    /// The hash used to generate each key's coefficient.
    coeff_hash: H,
    /// The hash used to generate the nonce coefficients.
    nonce_coeff_hash: H,
    /// The instance of the underlying Schnorr context.
    pub schnorr: Schnorr<H, NG>,
    /// The nonce generator used to
    nonce_gen: NG,
}

impl<H, NG> MuSig<H, NG> {
    /// Create a new keypair.
    ///
    /// A shorthand for [`KeyPair::new`].
    ///
    /// [`KeyPair::new`]: KeyPair::<Normal>::new
    pub fn new_keypair(&self, secret_key: Scalar) -> KeyPair {
        KeyPair::<Normal>::new(secret_key)
    }

    /// Gets the nonce generator from the underlying Schnorr instance.
    pub fn nonce_gen(&self) -> &NG {
        &self.nonce_gen
    }

    /// Generate nonces for creating signatures shares.
    ///
    /// ⚠ You must use a CAREFULLY CHOSEN nonce rng, see [`MuSig::seed_nonce_rng`]
    pub fn gen_nonce<R: RngCore>(&self, nonce_rng: &mut R) -> NonceKeyPair {
        NonceKeyPair::random(nonce_rng)
    }
}

impl<H, NG> MuSig<H, NG>
where
    H: Tag + Default,
    NG: Tag + Clone,
{
    /// Create a new MuSig instance from a [`Schnorr`] instance.
    ///
    /// The MuSig instnace will clone and tag the schnorr instance's `nonce_gen` for its own use.
    pub fn new(schnorr: Schnorr<H, NG>) -> Self {
        Self {
            pk_hash: H::default().tag(b"KeyAgg list"),
            coeff_hash: H::default().tag(b"KeyAgg coefficient"),
            nonce_coeff_hash: H::default().tag(b"MuSig/noncecoef"),
            nonce_gen: schnorr.nonce_gen().clone().tag(b"MuSig"),
            schnorr,
        }
    }
}

impl<H, NG> Default for MuSig<H, NG>
where
    H: Tag + Default,
    NG: Default + Clone + Tag,
{
    fn default() -> Self {
        MuSig::new(Schnorr::<H, NG>::default())
    }
}

/// A list of keys aggregated into a single key.
///
/// Created using [`MuSig::new_agg_key`].
///
/// The `AggKey` can't be serialized but it's very efficient to re-create it from the initial list of keys.
///
/// [`MuSig::new_agg_key`]
#[derive(Debug, Clone)]
pub struct AggKey<T> {
    /// The keys involved in the key aggregation.
    keys: Vec<Point>,
    /// The coefficients of each key
    coefs: Vec<Scalar<Public>>,
    /// Whether the secret keys needs to be negated when signing
    needs_negation: bool,
    /// The aggregate key
    agg_key: Point<T>,
    /// The tweak on the aggregate key
    tweak: Scalar<Public, Zero>,

    treekeys: Option<HashMap<usize, Point<Normal>>>,

    treecoefs: Option<HashMap<usize, Scalar<Public>>>,

    treecumulcoefs: Option<HashMap<usize, Scalar<Public>>>,
}

impl<T: Copy> AggKey<T> {
    /// The aggregate key.
    ///
    /// Note that before using it as a key in a system that accepts "x-only" keys like `[BIP341]`
    /// you must call [`into_xonly_key`] and use that aggregate key.
    ///
    /// [`into_xonly_key`]: Self::into_xonly_key
    pub fn agg_public_key(&self) -> Point<T> {
        self.agg_key
    }

    /// An iterator over the **public keys** of each party in the aggregate key.
    pub fn keys(&self) -> impl Iterator<Item = Point> + '_ {
        self.keys.iter().copied()
    }

    //Some getters with defensive copying
    pub fn get_coefs(&self) -> Vec<Scalar<Public>> {
        self.coefs.clone()
    }

    pub fn get_treekeys(&self) -> Option<HashMap<usize, Point<Normal>>> {
        self.treekeys.clone()
    }

    pub fn get_treecoefs(&self) -> Option<HashMap<usize, Scalar<Public>>> {
        self.treecoefs.clone()
    }

    pub fn get_treecumulcoefs(&self) -> Option<HashMap<usize, Scalar<Public>>> {
        self.treecumulcoefs.clone()
    }

    //Public key participation proof - maybe it belongs to <Normal>?
    //if successful, the proof is a vector of public keys: first the root, then the sibling of each level
    //assumptions: only the root and the leaves can have less than 4 children
    pub fn generate_simple_proof(&self, pk: Point<Normal>) -> Result<Vec<Point<Normal>>, String> {
        if self.treekeys.is_none() {
            return Err("Not a merkleized aggregation".to_string());
        }
        let treekeys = self.treekeys.as_ref().unwrap();
        let treecoefs = self.treecoefs.as_ref().expect("treecoefs not found");
        let treecumulcoefs = self
            .treecumulcoefs
            .as_ref()
            .expect("treecumulcoefs not found");
        match self.keys.len() {
            0 => return Err("No keys to generate proof".to_string()),
            1 => {
                if self.keys[0] == pk {
                    return Ok(vec![pk]);
                } else {
                    return Err("Key not found".to_string());
                }
            }
            _ => {}
        }

        // Construct the tree and aggregated keys
        let tree = ark::tree::Tree::new(self.keys.len());

        // Locate the position of `pk` in the tree leaves
        let index = self
            .keys
            .iter()
            .enumerate()
            .find(|(_idx, &ipk)| ipk == pk)
            .map(|(idx, _)| idx)
            .ok_or_else(|| "Key not found".to_string())?;

        let mut proof = vec![pk];

        let mut pix = tree.parent_idx_of_with_sibling_idx(index);

        for node in tree.iter_branch(index) {
            for (childidx, cix) in node.children().enumerate() {
                if let Some((_, sibling_idx)) = pix {
                    if sibling_idx != childidx {
                        proof.push(treekeys[&cix].clone()); // Collect sibling key
                    }
                }
            }

            // Update parent index and sibling index for the next iteration
            pix = tree.parent_idx_of_with_sibling_idx(node.idx());
            if pix.is_none() {
                // If we've reached the root, stop
                break;
            }
        }
        let rootkey = treekeys[&tree.root().idx()].clone();

        proof.push(rootkey);
        return Ok(proof);
    }
}

impl AggKey<Normal> {
    /// Convert the key into a BIP340 AggKey.
    ///
    /// This is the [BIP340] x-only version of the key which you can put in a segwitv1 output
    /// and create/verify BIP340 signatures under.
    ///
    /// [BIP340]: https://bips.xyz/340
    pub fn into_xonly_key(self) -> AggKey<EvenY> {
        let (agg_key, needs_negation) = self.agg_key.into_point_with_even_y();
        let mut tweak = self.tweak;
        tweak.conditional_negate(needs_negation);
        AggKey {
            keys: self.keys,
            coefs: self.coefs,
            needs_negation,
            tweak,
            agg_key,
            treekeys: None,
            treecoefs: None,
            treecumulcoefs: None,
        }
    }

    /// Add a scalar `tweak` to aggregate MuSig public key.
    ///
    /// The resulting key is equal to the existing key plus `tweak * G`. The tweak mutates the
    /// public key while still allowing the original set of signers to sign under the new key.
    /// This function is appropriate for doing [BIP32] tweaks before calling `into_xonly_key`.
    /// It **is not** appropriate for doing taproot tweaking which must be done on an [`AggKey`]
    /// with [`EvenY`] public key in BIP340 form, see [`into_xonly_key`].
    ///
    /// ## Return value
    ///
    /// In the erroneous case that the tweak is exactly equal to the negation of the aggregate
    /// secret key it returns `None`.
    ///
    /// [BIP32]: https://bips.xyz/32
    /// [`AggKey`]: crate::musig::AggKey
    /// [`into_xonly_key`]: crate::musig::AggKey::into_xonly_key
    pub fn tweak(self, tweak: Scalar<impl Secrecy, impl ZeroChoice>) -> Option<Self> {
        let agg_key = g!(self.agg_key + tweak * G).normalize().non_zero()?;
        let tweak = s!(self.tweak + tweak).public();

        Some(AggKey {
            keys: self.keys,
            coefs: self.coefs,
            needs_negation: false,
            agg_key,
            tweak,
            treekeys: self.treekeys,
            treecoefs: self.treecoefs,
            treecumulcoefs: self.treecumulcoefs,
        })
    }
}

// /// A [`AggKey`] that has been converted into a [BIP340] x-only key.
// ///
// /// [BIP340]: https://bips.xyz/340
impl AggKey<EvenY> {
    /// Applies an "x-only" tweak to the aggregate key.
    ///
    /// This function exists to allow for [BIP341] tweaks to the aggregate public key.
    ///
    /// [BIP341]: https://bips.xyz/341
    pub fn tweak(self, tweak: Scalar<impl Secrecy, impl ZeroChoice>) -> Option<Self> {
        let (new_agg_key, needs_negation) = g!(self.agg_key + tweak * G)
            .normalize()
            .non_zero()?
            .into_point_with_even_y();
        let mut new_tweak = s!(self.tweak + tweak).public();
        new_tweak.conditional_negate(needs_negation);
        let needs_negation = self.needs_negation ^ needs_negation;

        Some(Self {
            keys: self.keys,
            coefs: self.coefs,
            needs_negation,
            tweak: new_tweak,
            agg_key: new_agg_key,
            treekeys: self.treekeys,
            treecoefs: self.treecoefs,
            treecumulcoefs: self.treecumulcoefs,
        })
    }
}

impl<H: Digest<OutputSize = U32> + Clone, NG> MuSig<H, NG> {
    /// Generates a new aggregated key from a list of individual keys.
    ///
    /// Each party can be local (you know the secret key) or remote (you only know the public key).
    ///
    /// ## Example
    ///
    /// ```
    /// use schnorr_fun::{
    ///     fun::{Point, Scalar},
    ///     musig::MuSig,
    ///     nonce::Deterministic,
    ///     Schnorr,
    /// };
    /// # let my_secret_key = Scalar::random(&mut rand::thread_rng());
    /// # let their_public_key = Point::random(&mut rand::thread_rng());
    /// use sha2::Sha256;
    /// let musig = MuSig::<Sha256, Deterministic<Sha256>>::default();
    /// let my_keypair = musig.new_keypair(my_secret_key);
    /// let my_public_key = my_keypair.public_key();
    /// // Note the keys have to come in the same order on the other side!
    /// let agg_key = musig.new_agg_key(vec![their_public_key, my_public_key]);
    /// ```
    pub fn new_agg_key(&self, keys: Vec<Point>) -> AggKey<Normal> {
        let coeff_hash = {
            let L = self.pk_hash.clone().add(&keys[..]).finalize();
            self.coeff_hash.clone().add(L.as_slice())
        };

        let mut second = None;
        let coefs = keys
            .iter()
            .map(|key| {
                // This is the logic for IsSecond from appendix B of the MuSig2 paper
                if second.is_none() && key != &keys[0] {
                    second = Some(key);
                }
                if second != Some(key) {
                    Scalar::from_hash(coeff_hash.clone().add(key))
                } else {
                    Scalar::one()
                }
                .public()
            })
            .collect::<Vec<_>>();

        let agg_key = g!(&coefs .* &keys)
            .non_zero().expect("computationally unreachable: linear combination of hash randomised points cannot add to zero");

        AggKey {
            keys,
            coefs,
            agg_key: agg_key.normalize(),
            tweak: Scalar::zero(),
            needs_negation: false,
            treekeys: None,
            treecoefs: None,
            treecumulcoefs: None,
        }
    }

    pub fn new_merkleized_agg_key(&self, keys: Vec<Point>) -> AggKey<Normal> {
        if keys.len() <= 4 {
            return self.new_agg_key(keys);
        }

        let tree = ark::tree::Tree::new(keys.len());

        //calculate all partial coefficients
        let mut treekeys: HashMap<usize, Point<Normal>> =
            keys.iter().map(|key| key.clone()).enumerate().collect();
        let mut treecoefs = HashMap::new();
        let agg_key = recursive_key_aggregation(&tree, tree.root(), &mut treekeys, &mut treecoefs)
            .expect("computationally unreachable: all keys are valid");

        //calculate cumolative coefficients
        let mut cumulcoefs: HashMap<usize, Scalar<Public>> = HashMap::new();
        recursive_coef_cumulation(&tree, tree.root(), &treecoefs, &mut cumulcoefs);
        let mut coefs: Vec<Scalar<Public>> = Vec::new();
        for i in 0..keys.len() {
            coefs.push(cumulcoefs.get(&i).unwrap().clone());
        }

        AggKey {
            keys,
            coefs,
            agg_key: agg_key.normalize(),
            tweak: Scalar::zero(),
            needs_negation: false,
            treekeys: Some(treekeys),
            treecoefs: Some(treecoefs),
            treecumulcoefs: Some(cumulcoefs),
        }
    }
}

impl<H, NG> MuSig<H, NG>
where
    H: Digest<OutputSize = U32> + Clone,
    NG: NonceGen,
{
    /// Seed a random number generator to be used for MuSig nonces.
    ///
    /// ** ⚠ WARNING ⚠**: This method is unstable and easy to use incorrectly. The seed it uses for
    /// the Rng will change without warning between minor versions of this library.
    ///
    /// Parameters:
    ///
    /// - `agg_key`: the joint public key we are signing under. This can be an `XOnly` or `Normal`.
    ///    It will return the same nonce regardless.
    /// - `secret`: you're secret key as part of `agg_key`. This **must be the secret key you are
    /// going to sign with**. It cannot be an "untweaked" version of the signing key. It must be
    /// exactly equal to the secret key you pass to [`sign`] (the MuSig specification requires this).
    /// - `session_id`: a string of bytes that is **unique for each signing attempt**.
    ///
    /// The application should decide upon a unique `session_id` per call to this function. If the
    /// `NonceGen` of this MuSig instance is `Deterministic` then the `session_id` **must** be
    /// unique per signing attempt -- even if the signing attempt fails to produce a signature you
    /// must not reuse the session id, the resulting rng or anything derived from that rng again.
    ///
    /// 💡 Before using this function write a short justification as to why your beleive your session
    /// id will be unique per signing attempt. Perhaps include it as a comment next to the call.
    /// Note **it must be unique even across signing attempts for the same or different messages**.
    ///
    /// The rng returned can be used to create many nonces. For example, when signing a Bitcoin
    /// transaction you may need to sign several inputs each with their own signature. It is
    /// intended here that you call `seed_nonce_rng` once for the transaction and pull several nonces
    /// out of the resulting rng.
    ///
    /// [`sign`]: MuSig::sign
    pub fn seed_nonce_rng<R: SeedableRng<Seed = [u8; 32]>>(
        &self,
        agg_key: &AggKey<impl Normalized>,
        secret: &Scalar,
        session_id: &[u8],
    ) -> R {
        let sid_len = (session_id.len() as u64).to_be_bytes();
        let pk_bytes = agg_key.agg_public_key().to_xonly_bytes();

        let rng: R = secp256kfun::derive_nonce_rng!(
            nonce_gen => self.nonce_gen(),
            secret => &secret,
            public => [pk_bytes, sid_len, session_id],
            seedable_rng => R
        );
        rng
    }
}

//verifies that
//a) the proof starts with the leaf_key provided,
//b) processing the first len-1 keys in the proof generated the last one,
//c) and that the last key is equal to the root provided
pub fn verify_simple_proof(
    leaf_key: &Point<Normal>,
    root_key: &Point<Normal>,
    proof: Vec<Point<Normal>>,
) -> Result<(), String> {
    if proof.is_empty() {
        return Err("Empty proof".to_string());
    }
    //check if the root is at the end
    if proof.last() != Some(root_key) {
        return Err("Root key not in the proof".to_string());
    }

    //check if the leaf is in the proof
    if proof.first() != Some(leaf_key) {
        return Err("Key not in the proof".to_string());
    }

    let mut start = 1;
    let mut prev_key = *leaf_key;
    while start < proof.len() - 1 {
        let stop = (start + 3).min(proof.len() - 1);
        let mut sibling_keys = vec![prev_key];
        sibling_keys.extend(&proof[start..stop]);

        let musig = self::new_with_deterministic_nonces::<sha2::Sha256>();
        sibling_keys.sort();
        prev_key = musig.new_agg_key(sibling_keys).agg_public_key();

        start = stop;
    }
    if prev_key != *root_key {
        return Err("Root key not correct".to_string());
    }
    Ok(())
}

fn recursive_coef_cumulation(
    tree: &ark::tree::Tree,
    node: &ark::tree::Node,
    coefs: &HashMap<usize, Scalar<Public>>,
    cumulcoefs: &mut HashMap<usize, Scalar<Public>>,
) {
    if node.is_root() {
        cumulcoefs.insert(node.idx(), Scalar::one());
    }
    for child in node.children() {
        let a = cumulcoefs.get(&node.idx()).unwrap();
        let b = coefs.get(&child).unwrap();
        let c = op::scalar_mul(a, b);
        let c = c.set_secrecy::<Public>();
        cumulcoefs.insert(child, c);
        let child_node = get_node_hack(tree, child);
        recursive_coef_cumulation(tree, child_node, coefs, cumulcoefs);
    }
}

fn recursive_key_aggregation(
    tree: &ark::tree::Tree,
    node: &ark::tree::Node,
    leaf_keys: &mut HashMap<usize, Point<Normal>>,
    coeffs: &mut HashMap<usize, Scalar<Public>>,
) -> Result<Point<Normal>, String> {
    let iskey = leaf_keys.get(&node.idx());
    if node.is_leaf() {
        let key = leaf_keys.get(&node.idx()).expect("Key not found");
        return Ok(key.clone());
    }
    if iskey.is_some() {
        println!(
            "Key already found at {:?}. This should not have happened...",
            node.idx()
        );
    }

    // Collect aggregated keys from child nodes
    let mut sibling_keys = Vec::<Point>::new();
    for child in node.children() {
        let child_node = get_node_hack(tree, child);
        let rkey = recursive_key_aggregation(tree, child_node, leaf_keys, coeffs);
        if let Ok(key) = rkey {
            sibling_keys.push(key);
        } else {
            return Err("Error in recursive key aggregation".to_string());
        }
    }

    //agg_keys sugar sorts the keys before aggregating, but returns the coefs un-sorted
    let (node_key, coefs) = agg_keys(&sibling_keys);

    // Store the aggregated key in leaf_keys and return it
    leaf_keys.insert(node.idx(), node_key.clone());

    // Store the coefficients in the coefficients map
    for (i, coef) in coefs.iter().enumerate() {
        coeffs.insert(node.children().nth(i).unwrap(), coef.clone());
    }
    if node.is_root() {
        coeffs.insert(node.idx(), Scalar::one());
    }

    Ok(node_key)
}

fn agg_keys(keys: &Vec<Point>) -> (Point<Normal>, Vec<Scalar<Public>>) {
    let musig = self::new_with_deterministic_nonces::<sha2::Sha256>();
    let mut mkeys = keys.clone();
    let mut unsort: Vec<usize> = (0..keys.len()).collect();
    unsort.sort_by(|&a, &b| keys[a].cmp(&keys[b]));
    mkeys.sort();
    let kagg = musig.new_agg_key(mkeys);

    let mut cu = kagg.coefs.iter().enumerate().collect::<Vec<_>>();
    cu.sort_by_key(|&(i, _)| unsort[i]);
    let c = cu.into_iter().map(|(_, c)| c.clone()).collect();
    (kagg.agg_public_key(), c)
}

fn get_node_hack(tree: &ark::tree::Tree, idx: usize) -> &ark::tree::Node {
    tree.iter().nth(idx).unwrap()
}

/// Marker type for indicating the [`SignSession`] is being used to create an ordinary Schnorr
/// signature.
#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(
    feature = "serde",
    derive(crate::fun::serde::Deserialize, crate::fun::serde::Serialize),
    serde(crate = "crate::fun::serde")
)]
#[cfg_attr(
    feature = "bincode",
    derive(crate::fun::bincode::Encode, crate::fun::bincode::Decode),
    bincode(crate = "crate::fun::bincode")
)]
pub struct Ordinary;

/// Marks the [`SignSession`] as being used to create an adaptor (a.k.a. one-time encrypted)
/// signature.
#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(
    feature = "serde",
    derive(crate::fun::serde::Deserialize, crate::fun::serde::Serialize),
    serde(crate = "crate::fun::serde")
)]
#[cfg_attr(
    feature = "bincode",
    derive(crate::fun::bincode::Encode, crate::fun::bincode::Decode),
    bincode(crate = "crate::fun::bincode")
)]
pub struct Adaptor {
    y_needs_negation: bool,
}

/// A signing session.
///
/// Created by [`start_sign_session`] or [`start_encrypted_sign_session`].
/// The type parameter records whether you are trying to jointly generate a signature or an adaptor signature.
///
/// [`start_sign_session`]: MuSig::start_sign_session
/// [`start_encrypted_sign_session`]: MuSig::start_encrypted_sign_session
/// [`sign`]: MuSig::sign
#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(
    feature = "serde",
    derive(crate::fun::serde::Deserialize, crate::fun::serde::Serialize),
    serde(crate = "crate::fun::serde")
)]
#[cfg_attr(
    feature = "bincode",
    derive(crate::fun::bincode::Encode, crate::fun::bincode::Decode),
    bincode(crate = "crate::fun::bincode")
)]
pub struct SignSession<T = Ordinary> {
    b: Scalar<Public, Zero>,
    c: Scalar<Public, Zero>,
    public_nonces: Vec<Nonce>,
    R: Point<EvenY>,
    nonce_needs_negation: bool,
    signing_type: T,
}

impl<H: Digest<OutputSize = U32> + Clone, NG> MuSig<H, NG> {
    /// Start a signing session.
    ///
    /// You must provide the public nonces for this signing session in the correct order.
    ///
    /// ## Return Value
    ///
    /// Returns `None` in the case that the `remote_nonces` have been (maliciously) selected to
    /// cancel out your local nonces.
    /// This is not a security issue -- we just can't continue the protocol if this happens.
    ///
    /// # Panics
    ///
    /// Panics if number of nonces does not align with the keys in `agg_key`.
    pub fn start_sign_session(
        &self,
        agg_key: &AggKey<EvenY>,
        nonces: Vec<Nonce>,
        message: Message<'_, Public>,
    ) -> SignSession {
        let (b, c, public_nonces, R, nonce_needs_negation) = self._start_sign_session(
            agg_key,
            nonces,
            message,
            &Point::<Normal, Public, _>::zero(),
        );
        SignSession {
            b,
            c,
            public_nonces,
            R,
            nonce_needs_negation,
            signing_type: Ordinary,
        }
    }

    /// Start an encrypted signing session.
    ///
    /// i.e. a session to produce an adaptor signature under `encryption_key`.
    /// See [`adaptor`] for a more general description of adaptor signatures.
    ///
    /// You must provide the public nonces (where your public portions must be
    /// shared with the other signer(s)).
    ///
    /// ## Return Value
    ///
    /// Returns `None` in the case that the `remote_nonces` have been (maliciously) selected to
    /// cancel out your local nonces.
    /// This is not a security issue -- we just can't continue the protocol if this happens.
    ///
    /// # Panics
    ///
    /// Panics if number of local or remote nonces passed in does not align with the keys in
    /// `agg_key`.
    ///
    /// [`adaptor`]: crate::adaptor
    pub fn start_encrypted_sign_session(
        &self,
        agg_key: &AggKey<EvenY>,
        nonces: Vec<Nonce>,
        message: Message<'_, Public>,
        encryption_key: &Point<impl PointType, impl Secrecy, impl ZeroChoice>,
    ) -> Option<SignSession<Adaptor>> {
        let (b, c, public_nonces, R, nonce_needs_negation) =
            self._start_sign_session(agg_key, nonces, message, encryption_key);
        Some(SignSession {
            b,
            c,
            public_nonces,
            R,
            nonce_needs_negation,
            signing_type: Adaptor {
                y_needs_negation: nonce_needs_negation,
            },
        })
    }

    #[allow(clippy::type_complexity)]
    fn _start_sign_session(
        &self,
        agg_key: &AggKey<EvenY>,
        nonces: Vec<Nonce>,
        message: Message<'_, Public>,
        encryption_key: &Point<impl PointType, impl Secrecy, impl ZeroChoice>,
    ) -> (
        Scalar<Public, Zero>,
        Scalar<Public, Zero>,
        Vec<Nonce>,
        Point<EvenY>,
        bool,
    ) {
        let mut Rs = nonces;
        let agg_Rs = Rs.iter().fold([Point::zero(); 2], |acc, nonce| {
            [g!(acc[0] + nonce.0[0]), g!(acc[1] + nonce.0[1])]
        });
        let agg_Rs = Nonce::<Zero>([
            g!(agg_Rs[0] + encryption_key).normalize(),
            agg_Rs[1].normalize(),
        ]);

        let b = {
            let H = self.nonce_coeff_hash.clone();
            Scalar::from_hash(
                H.add(agg_Rs.to_bytes())
                    .add(agg_key.agg_public_key())
                    .add(message),
            )
        }
        .public()
        .mark_zero();

        let (R, r_needs_negation) = g!(agg_Rs.0[0] + b * agg_Rs.0[1])
            .normalize()
            .non_zero()
            .unwrap_or(Point::generator())
            .into_point_with_even_y();

        for R_i in &mut Rs {
            R_i.conditional_negate(r_needs_negation);
        }

        let c = self
            .schnorr
            .challenge(&R, &agg_key.agg_public_key(), message);

        (b, c, Rs, R, r_needs_negation)
    }

    /// Generates a partial signature (or partial encrypted signature depending on `T`) for the local_secret_nonce.
    pub fn sign<T>(
        &self,
        agg_key: &AggKey<EvenY>,
        session: &SignSession<T>,
        my_index: usize,
        keypair: &KeyPair,
        local_secret_nonce: NonceKeyPair,
    ) -> Scalar<Public, Zero> {
        assert_eq!(
            keypair.public_key(),
            agg_key.keys().nth(my_index).unwrap(),
            "key at index {my_index} didn't match",
        );
        let c = session.c;
        let b = session.b;
        let x_i = keypair.secret_key();
        let mut a = agg_key.coefs[my_index];

        a.conditional_negate(agg_key.needs_negation);
        let [mut r1, mut r2] = local_secret_nonce.secret;
        r1.conditional_negate(session.nonce_needs_negation);
        r2.conditional_negate(session.nonce_needs_negation);
        s!(c * a * x_i + r1 + b * r2).public()
    }

    #[must_use]
    /// Verifies a partial signature (or partial encrypted signature depending on `T`).
    ///
    /// You must provide the `index` of the party (the index of the key in `agg_key`).
    ///
    /// # Panics
    ///
    /// Panics when `index` is equal to or greater than the number of keys in the agg_key.
    pub fn verify_partial_signature<T>(
        &self,
        agg_key: &AggKey<EvenY>,
        session: &SignSession<T>,
        index: usize,
        partial_sig: Scalar<Public, Zero>,
    ) -> bool {
        let c = session.c;
        let b = session.b;
        let s_i = &partial_sig;
        let a = agg_key.coefs[index];

        let X_i = agg_key
            .keys()
            .nth(index)
            .unwrap()
            .conditional_negate(agg_key.needs_negation);

        let [R1, R2] = &session.public_nonces[index].0;
        g!((c * a) * X_i + R1 + b * R2 - s_i * G).is_zero()
    }

    /// Combines all the partial signatures into a single `Signature`.
    ///
    /// Note this does not check the validity of any of the partial signatures. You should either check
    /// each one using [`verify_partial_signature`] or use [`verify`] on the returned `Signature` to check validity.
    ///
    /// [`verify`]: crate::Schnorr::verify
    /// [`verify_partial_signature`]: Self::verify_partial_signature
    pub fn combine_partial_signatures(
        &self,
        agg_key: &AggKey<EvenY>,
        session: &SignSession<Ordinary>,
        partial_sigs: impl IntoIterator<Item = Scalar<Public, Zero>>,
    ) -> Signature {
        let (R, s) = self._combine_partial_signatures(agg_key, session, partial_sigs);
        Signature { R, s }
    }

    /// Combines all the partial encrypted signatures into one encrypted signature.
    ///
    /// Note this does not check the validity of any of the partial signatures. You should either check
    /// each one using [`verify_partial_signature`] or use [`verify_encrypted_signature`] on the returned `Signature` to check validity.
    ///
    /// [`verify_encrypted_signature`]: crate::adaptor::Adaptor::verify_encrypted_signature
    /// [`verify_partial_signature`]: Self::verify_partial_signature
    pub fn combine_partial_encrypted_signatures(
        &self,
        agg_key: &AggKey<EvenY>,
        session: &SignSession<Adaptor>,
        partial_encrypted_sigs: impl IntoIterator<Item = Scalar<Public, Zero>>,
    ) -> EncryptedSignature {
        let (R, s_hat) = self._combine_partial_signatures(agg_key, session, partial_encrypted_sigs);
        EncryptedSignature {
            R,
            s_hat,
            needs_negation: session.signing_type.y_needs_negation,
        }
    }

    fn _combine_partial_signatures<T>(
        &self,
        agg_key: &AggKey<EvenY>,
        session: &SignSession<T>,
        partial_sigs: impl IntoIterator<Item = Scalar<Public, Zero>>,
    ) -> (Point<EvenY>, Scalar<Public, Zero>) {
        let sum_s = partial_sigs
            .into_iter()
            .reduce(|acc, s| s!(acc + s).public())
            .unwrap_or(Scalar::zero());

        let s = s!(sum_s + agg_key.tweak * session.c).public();

        (session.R, s)
    }
}

/// Constructor for a MuSig instance using deterministic nonce generation.
///
/// If you use deterministic nonce generation you will have to provide a unique session id to every
/// signing session. The advantage is that you will be able to regenerate the same nonces at a later
/// point from [`MuSig::seed_nonce_rng`].
///
/// ```
/// use schnorr_fun::musig;
/// let musig = musig::new_with_deterministic_nonces::<sha2::Sha256>();
/// ```
pub fn new_with_deterministic_nonces<H>() -> MuSig<H, nonce::Deterministic<H>>
where
    H: Tag + Digest<OutputSize = U32> + Default + Clone,
{
    MuSig::default()
}

/// Constructor for a MuSig instance using synthetic nonce generation.
///
/// Sythetic nonce generation mixes in external randomness into nonce generation which means you
/// don't need a unique session id for each signing session to guarantee security. The disadvantage
/// is that you may have to store and recall somehow the nonces generated from
/// [`MuSig::seed_nonce_rng`].
///
/// ```
/// use schnorr_fun::musig;
/// let musig = musig::new_with_synthetic_nonces::<sha2::Sha256, rand::rngs::ThreadRng>();
/// ```
pub fn new_with_synthetic_nonces<H, R>() -> MuSig<H, nonce::Synthetic<H, nonce::GlobalRng<R>>>
where
    H: Tag + Digest<OutputSize = U32> + Default + Clone,
    R: RngCore + Default + Clone,
{
    MuSig::default()
}

/// Create a MuSig instance which does not handle nonce generation.
///
/// You can still sign with this instance but you you will have to generate nonces in your own way.
pub fn new_without_nonce_generation<H>() -> MuSig<H, NoNonces>
where
    H: Tag + Digest<OutputSize = U32> + Default,
{
    MuSig::default()
}
