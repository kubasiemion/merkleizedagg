A simple test of the idea of aggregating Schnorr PublicKeys using a "merkleized" structure, 
thus allowing for short proofs of participation in an aggregation

There are three main methods:

1) The aggregation
```
// returns the aggregated key, as well as all the keys in the tree of radix 4
// the tree keys contain all the original keys at the beginning of the vector, but sorted
pub fn merkelized_key_aggregation(pubkeys: Vec<PublicKey>) -> (PublicKey, Vec<PublicKey>) 
```
2) The proof
```
// hopefully returns the Merkle proof of the pk participation in the aggregation of pkleaves
pub fn generate_inclusion_proof(
    pk: PublicKey,
    pkleaves: Vec<PublicKey>,
) -> Result<InclusionProof, String>
```
where the ```InclusionProof``` contains the proof tree and the leaf- and intermediate keys (this would be simple if I have included the keys in tree nodes as members, but this is not the case)
```
pub struct InclusionProof {
    tree: Tree,
    keys: Vec<PublicKey>,
}
```
4) The proof verification. 
```
// returns true if the leaf_key is included in the proof leaves (of which there are up to 4),
// and if the tree evaluation is equal to the root_key
pub fn verify_inclusion_proof(
    leaf_key: &PublicKey,
    root_key: &PublicKey,
    proof: InclusionProof,
) -> bool
´´´


