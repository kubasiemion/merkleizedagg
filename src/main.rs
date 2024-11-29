use once_cell::sync::Lazy;
use secp256k1_zkp::{MusigKeyAggCache, PublicKey, Secp256k1};
use std::collections::HashMap;
use std::vec;

static SECP: Lazy<Secp256k1<secp256k1_zkp::All>> = Lazy::new(Secp256k1::new);

pub fn main() {
    println!("Hello, world!");
}

pub fn generate_tree_keys(
    pubkeys: &Vec<PublicKey>,
) -> Result<(PublicKey, HashMap<usize, PublicKey>), String> {
    let tree = ark::tree::Tree::new(pubkeys.len());
    let mut treekeys: HashMap<usize, PublicKey> =
        pubkeys.iter().map(|key| key.clone()).enumerate().collect();
    match recursive_key_aggregation(&tree, tree.root(), &mut treekeys) {
        Ok(rootkey) => Ok((rootkey.clone(), treekeys)),
        Err(msg) => Err(msg),
    }
}

fn recursive_key_aggregation(
    tree: &ark::tree::Tree,
    node: &ark::tree::Node,
    leaf_keys: &mut HashMap<usize, PublicKey>,
) -> Result<PublicKey, String> {
    let iskey = leaf_keys.get(&node.idx());
    if node.is_leaf() {
        if let Some(key) = iskey {
            return Ok(key.clone());
        } else {
            return Err("Key not found".to_string());
        }
    }
    if iskey.is_some() {
        println!(
            "Key already found at {:?}. This should not have happened...",
            node.idx()
        );
    }

    // Collect aggregated keys from child nodes
    let sibling_keys: Vec<PublicKey> = node
        .children()
        .map(|child| recursive_key_aggregation(tree, get_node_hack(tree, child), leaf_keys))
        .collect::<Result<_, _>>()?; // Propagate errors

    // Aggregate the sibling keys into a new key
    let aggregated_key = key_agg(sibling_keys).agg_pk_full();

    // Store the aggregated key in leaf_keys and return it
    leaf_keys.insert(node.idx(), aggregated_key.clone());
    Ok(aggregated_key)
}

//unsafe hack
fn get_node_hack(tree: &ark::tree::Tree, idx: usize) -> &ark::tree::Node {
    tree.iter().nth(idx).unwrap()
}

//if successful, the proof is a vector of public keys: first the root, then the sibling of each level
//the assumptions: the keys are sorted, only the root and the leaves can have less than 4 children
pub fn generate_simple_proof(
    pk: PublicKey,
    pkleaves: Vec<PublicKey>,
) -> Result<Vec<PublicKey>, String> {
    match pkleaves.len() {
        0 => return Err("No keys to generate proof".to_string()),
        1 => {
            if pkleaves[0] == pk {
                return Ok(vec![pk]);
            } else {
                return Err("Key not found".to_string());
            }
        }
        _ => {}
    }

    // Construct the tree and aggregated keys
    let tree = ark::tree::Tree::new(pkleaves.len());
    let (rootkey, treekeys) = generate_tree_keys(&pkleaves)?;

    // Locate the position of `pk` in the tree leaves
    let index = pkleaves
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

    proof.push(rootkey);
    return Ok(proof);
}

pub fn verify_simple_proof(
    leaf_key: &PublicKey,
    root_key: &PublicKey,
    proof: Vec<PublicKey>,
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

        prev_key = key_agg(sibling_keys).agg_pk_full();

        start = stop;
    }
    if prev_key != *root_key {
        return Err("Root key not correct".to_string());
    }
    Ok(())
}

fn sort_pkeys(pubkeys: Vec<PublicKey>) -> Vec<PublicKey> {
    let mut keys = pubkeys;
    keys.sort_by_key(|k| k.serialize());
    keys
}

pub fn key_agg(keys: Vec<PublicKey>) -> MusigKeyAggCache {
    MusigKeyAggCache::new(&SECP, &sort_pkeys(keys))
}

#[cfg(test)]
mod test {
    use super::*;
    use rand::{RngCore, SeedableRng};
    use secp256k1_zkp::Keypair;

    fn generate_test_keys(leafcount: u32, state: u64) -> Vec<PublicKey> {
        let mut rand = rand::rngs::StdRng::seed_from_u64(state);
        let mut buffer = [0u8; 32];
        let mut pubkeys = Vec::new();
        //generate 9 new keys and put the public keys in the vector
        let mut errcount = 0;
        for _ in 0..leafcount {
            rand.fill_bytes(&mut buffer);
            if let Ok(pk) = Keypair::from_seckey_slice(&SECP, buffer.as_ref()) {
                pubkeys.push(pk.public_key());
            } else {
                errcount += 1;
            }
        }
        if errcount > 0 {
            println!("Error generating {} keys", errcount);
        }
        pubkeys
    }

    //Test generate_simple_proof()
    #[test]
    fn test_simple_proof() {
        let leafcount = 65;

        let pubkeys = generate_test_keys(leafcount, 45);
        let (rootkey, treekeys) =
            generate_tree_keys(&pubkeys).expect("Failed at merkle aggregation");
        let test_key_idx = 53;
        let key = treekeys.get(&test_key_idx).unwrap().clone();
        let proof = generate_simple_proof(key, pubkeys.clone());

        println!("Test key: {:?}", key);
        println!("Root key: {:?}", rootkey);

        match proof {
            Ok(proof) => {
                //proof.pop();
                println!("Proof keys: {:?}", proof.len());
                let res = verify_simple_proof(&key, &rootkey, proof);
                println!("Proof verified: {:?}", res);
            }
            Err(msg) => {
                println!("Error: {:?}", msg);
            }
        }
    }
}
