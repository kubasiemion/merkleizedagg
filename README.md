A simple test of the idea of aggregating Schnorr PublicKeys using a "merkleized" structure, 
thus allowing for short proofs of participation in an aggregation

There are three main methods:

1) The aggregation
```
//returns the aggregated key and the map node.idx->key
pub fn generate_tree_keys(
    pubkeys: &Vec<PublicKey>,
) -> Result<(PublicKey, HashMap<usize, PublicKey>), String>  
```
Internally it uses ark::tree::Tree to structure the aggregation

2) The proof
```
//if successful, the proof is a vector of public keys: first the root, then the sibling of each level
//assumptions: only the root and the leaves can have less than 4 children
pub fn generate_simple_proof(
    pk: PublicKey,
    pkleaves: Vec<PublicKey>,
) -> Result<Vec<PublicKey>, String>
```
The proof is a vector of public keys. The first key is the key that goes into the aggregation (a leaf key). 
The last key is the aggregated key.


3) The proof verification. 
```
//verifies that
//a. the proof starts with the leaf_key provided,
//b. processing the first len-1 keys in the proof generated the last one,
//c. and that the last key is equal to the root provided
pub fn verify_simple_proof(
    leaf_key: &PublicKey,
    root_key: &PublicKey,
    proof: Vec<PublicKey>,
) -> Result<(), String> 
´´´
There is redundancy, ofc. 


