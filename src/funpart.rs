use secp256kfun::op;
use secp256kfun::{g, marker, KeyPair, Point, Scalar, G};

//use rand_chacha::ChaCha20Rng;
use rand::{RngCore, SeedableRng};
use rand_chacha::ChaCha20Rng;
use schnorr_fun::binonce::NonceKeyPair;
use schnorr_fun::musig::AggKey;
use schnorr_fun::{nonce, Message, Schnorr};
use sha2::Sha256;
use std::collections::HashMap;

use crate::mmusig;
//use secp256kfun::rand_core

//a hack
fn get_node_hack(tree: &ark::tree::Tree, idx: usize) -> &ark::tree::Node {
    tree.iter().nth(idx).unwrap()
}

fn verify_node(
    node: &ark::tree::Node,
    keys: HashMap<usize, Point<marker::Normal>>,
    coefs: HashMap<usize, Scalar<marker::Public>>,
) -> Result<(), String> {
    let nodekey = keys.get(&node.idx()).expect("Node key not found");
    let childkeys: Vec<_> = node
        .children()
        .filter_map(|child| keys.get(&child))
        .collect();
    let coefs: Vec<_> = node
        .children()
        .filter_map(|child| coefs.get(&child))
        .collect();

    let T = g!(coefs .* childkeys);
    if T.eq(nodekey) {
        return Ok(());
    } else {
        return Err("Verification failed".to_string());
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::mmusig;

    fn generate_test_keys(leafcount: u32, state: u64) -> Vec<Point<marker::Normal>> {
        let mut rand = rand::rngs::StdRng::seed_from_u64(state);
        let mut buffer = [0u8; 32];
        let mut pubkeys = Vec::new();
        //generate 9 new keys and put the public keys in the vector
        let mut errcount = 0;
        for _ in 0..leafcount {
            rand.fill_bytes(&mut buffer);
            if let Some(scalar) = Scalar::from_bytes(buffer) {
                let keypair = KeyPair::<marker::Normal>::new(scalar);
                pubkeys.push(keypair.public_key());
            } else {
                errcount += 1;
            }
            if errcount > 0 {
                println!("Error generating {} keys", errcount);
            }
        }

        pubkeys
    }

    #[test]
    fn test_wrapped() {
        let leafcount = 561;
        let leafkeys = generate_test_keys(leafcount, 44);
        let mmusig = mmusig::new_with_deterministic_nonces::<sha2::Sha256>();
        let agg_key = mmusig.new_merkleized_agg_key(leafkeys.clone());

        println!("Aggregated key: {:?}", agg_key.agg_public_key());

        let T = g!(agg_key.get_coefs() .* leafkeys);
        println!("T: {:?}", T);
    }

    #[test]
    fn test_wrapped_sign() {
        let schnorr = Schnorr::<Sha256, nonce::Deterministic<Sha256>>::default();
        let leafcount = 1561;

        let mut keys: Vec<KeyPair> = Vec::new();
        let mut rand = rand::rngs::StdRng::seed_from_u64(44);
        let mut buffer = [0u8; 32];
        //generate 9 new keys and put the public keys in the vector
        let mut errcount = 0;
        for _ in 0..leafcount {
            rand.fill_bytes(&mut buffer);
            if let Some(scalar) = Scalar::from_bytes(buffer) {
                let keypair = KeyPair::<marker::Normal>::new(scalar);
                keys.push(keypair);
            } else {
                errcount += 1;
            }
            if errcount > 0 {
                println!("Error generating {} keys", errcount);
            }
        }
        let pubkeys: Vec<_> = keys.iter().map(|key| key.public_key()).collect();

        let musig = mmusig::new_with_deterministic_nonces::<sha2::Sha256>();
        let start = std::time::Instant::now();
        let agg_key = musig.new_merkleized_agg_key(pubkeys.clone());

        let mut nonce_rng: ChaCha20Rng =
            musig.seed_nonce_rng(&agg_key, &keys[0].secret_key(), b"test");

        let xagg_key = agg_key.clone().into_xonly_key();

        let nonces: Vec<_> = keys
            .iter()
            .map(|key| musig.gen_nonce(&mut nonce_rng))
            .collect();

        let pubnonces: Vec<_> = nonces.iter().map(|nonce| nonce.public()).collect();

        let message = Message::<marker::Public>::plain(
            "my-app",
            b"chancellor on brink of second bailout for banks",
        );

        let signsession = musig.start_sign_session(&xagg_key, pubnonces.clone(), message.clone());

        //partial signatures
        let part_sigs: Vec<_> = keys
            .iter()
            .zip(nonces.iter())
            .enumerate()
            .map(|(id, (key, nonce))| {
                musig.sign(
                    &xagg_key,
                    &signsession,
                    *xagg_key.unsort(id).unwrap(),
                    //xagg_key.key_index(&key.public_key()).unwrap(),
                    key,
                    nonce.clone(),
                )
            })
            .collect();

        let sig = musig.combine_partial_signatures(&xagg_key, &signsession, part_sigs.clone());

        let ok = schnorr.verify(&xagg_key.agg_public_key(), message, &sig);
        let duration = start.elapsed();
        println!("Time elapsed in sign function is: {:?}", duration);
        println!("Aggregated Key: {:?}", xagg_key.agg_public_key());
        println!("Signature valid: {}", ok);

        println!("Tree coef: {:?}", agg_key.get_coefs().len());

        let pk = pubkeys[1];
        let p = agg_key.generate_simple_proof(pk);

        let pv = mmusig::verify_simple_proof(&pk, &agg_key.agg_public_key(), p.clone().unwrap());
        println!("Proof: {:?}", p.unwrap().len());
        println!("Proof verified: {:?}", pv);
    }

    #[test]
    fn test_std_sign() {
        let schnorr = Schnorr::<Sha256, nonce::Deterministic<Sha256>>::default();
        let leafcount = 1561;

        let start = std::time::Instant::now();
        let mut keys: Vec<KeyPair> = Vec::new();
        let mut rand = rand::rngs::StdRng::seed_from_u64(44);
        let mut buffer = [0u8; 32];
        //generate 9 new keys and put the public keys in the vector
        let mut errcount = 0;
        for _ in 0..leafcount {
            rand.fill_bytes(&mut buffer);
            if let Some(scalar) = Scalar::from_bytes(buffer) {
                let keypair = KeyPair::<marker::Normal>::new(scalar);
                keys.push(keypair);
            } else {
                errcount += 1;
            }
            if errcount > 0 {
                println!("Error generating {} keys", errcount);
            }
        }
        let pubkeys: Vec<_> = keys.iter().map(|key| key.public_key()).collect();

        let musig = mmusig::new_with_deterministic_nonces::<sha2::Sha256>();
        let start = std::time::Instant::now();
        let agg_key = musig.new_agg_key(pubkeys.clone());

        let mut nonce_rng: ChaCha20Rng =
            musig.seed_nonce_rng(&agg_key, &keys[0].secret_key(), b"test");

        let xagg_key = agg_key.clone().into_xonly_key();

        let nonces: Vec<_> = keys
            .iter()
            .map(|key| musig.gen_nonce(&mut nonce_rng))
            .collect();

        let pubnonces: Vec<_> = nonces.iter().map(|nonce| nonce.public()).collect();

        let message = Message::<marker::Public>::plain(
            "my-app",
            b"chancellor on brink of second bailout for banks",
        );

        let signsession = musig.start_sign_session(&xagg_key, pubnonces.clone(), message.clone());

        //partial signatures
        let part_sigs: Vec<_> = keys
            .iter()
            .zip(nonces.iter())
            .enumerate()
            .map(|(id, (key, nonce))| musig.sign(&xagg_key, &signsession, id, key, nonce.clone()))
            .collect();

        let sig = musig.combine_partial_signatures(&xagg_key, &signsession, part_sigs.clone());

        let ok = schnorr.verify(&xagg_key.agg_public_key(), message, &sig);
        let duration = start.elapsed();
        println!("Time elapsed in sign function is: {:?}", duration);
        println!("Aggregated Key: {:?}", xagg_key.agg_public_key());
        println!("Signature valid: {}", ok);
    }
}
