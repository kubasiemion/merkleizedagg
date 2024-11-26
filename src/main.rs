use once_cell::sync::Lazy;
use secp256k1_zkp::{MusigKeyAggCache, PublicKey, Secp256k1};
use std::cmp;

static SECP: Lazy<Secp256k1<secp256k1_zkp::All>> = Lazy::new(Secp256k1::new);

//Takes a vecor of public keys, returns the aggregated/rooot key,
//and a vector of all the keys in the tree, in order of the tree nodes
pub fn merkelized_key_aggregation(pubkeys: Vec<PublicKey>) -> (PublicKey, Vec<PublicKey>) {
    let tree = Tree::new(pubkeys.len());

    let mut tree_keys = sort_pkeys(pubkeys);
    let mut cursor = 0;
    loop {
        let parent = tree.parent_idx_of(cursor);
        if parent.is_none() {
            break; //root
        }
        let pidx = parent.unwrap();
        let pnodeopt = tree.nodes.get(pidx);
        if pnodeopt.is_none() {
            break; //error
        }
        let pnode = pnodeopt.unwrap();
        let mut sibling_keys = Vec::new();
        let childcount = pnode
            .children
            .iter()
            .filter_map(|child| child.map(|index| index as usize))
            .filter_map(|index| tree_keys.get(index)) // Safely handle missing indices
            .map(|nkey| {
                sibling_keys.push(nkey.clone()); // Push the cloned key
                nkey // Return the key to count the elements
            })
            .count();

        tree_keys.push(key_agg(sibling_keys).agg_pk_full());
        cursor += childcount;
    }
    let rootkey = tree_keys.get(tree.root().idx()).unwrap();
    (rootkey.clone(), tree_keys)
}

pub struct InclusionProof {
    tree: Tree,
    keys: Vec<PublicKey>,
}

pub fn generate_inclusion_proof(
    pk: PublicKey,
    pkleaves: Vec<PublicKey>,
) -> Result<InclusionProof, String> {
    // check if the key is in the leaves
    let sortedkeys = sort_pkeys(pkleaves);
    let index = sortedkeys.iter().position(|x| *x == pk);
    if index.is_none() {
        return Err("Key not found".to_string());
    }
    let mut cursor = index.unwrap();
    println!("Index: {:?}", index.unwrap());
    let tree = Tree::new(sortedkeys.len());
    let (_, treekeys) = merkelized_key_aggregation(sortedkeys);

    let proof_leaf_count = if tree.parent_idx_of(cursor).is_some() {
        tree.nodes
            .get(tree.parent_idx_of(cursor).unwrap())
            .unwrap()
            .children()
            .count()
    } else {
        1
    };

    let mut proofkeys = Vec::new();
    let mut proofnodes = Vec::new();
    let mut level = 0;
    let mut prevchildren: [Option<u32>; 4] = [None; 4]; //declared here so that the parent can use siblings as children

    loop {
        if let Some((o_parentix, o_sib_pos)) = tree.parent_idx_of_with_sibling_idx(cursor) {
            let o_parent = tree.nodes.get(o_parentix).unwrap();
            let mut p_parentix = o_parent.children().count() + proofnodes.len(); //we will insert the parent after all siblings

            //  unless...
            if let Some((_, parent_sib_pos)) = tree.parent_idx_of_with_sibling_idx(o_parentix) {
                p_parentix += parent_sib_pos;
            }

            let mut children = [None; 4];

            for (i, child) in o_parent.children.iter().enumerate() {
                if let Some(c_o_idx) = child {
                    let tkey = treekeys.get(*c_o_idx as usize).expect("Key should exist");

                    let c_p_idx = proofkeys.len(); //child index in the proof tree
                    children[i] = Some(c_p_idx as u32);
                    proofkeys.push(tkey.clone());
                    proofnodes.push(Node {
                        idx: c_p_idx as u32,
                        leaves: (0, 0),
                        children: if i == o_sib_pos {
                            prevchildren
                        } else {
                            [None; 4]
                        },
                        level: level,
                        parent: Some(p_parentix as u32),
                        nb_tree_leaves: 0,
                    });
                } else {
                    children[i] = None;
                }
            }
            prevchildren = children;
            // add the parent
            cursor = o_parentix;
        } else {
            //root
            proofnodes.push(Node {
                idx: proofnodes.len() as u32,
                leaves: (0, 0),
                children: prevchildren,
                level: level,
                parent: None,
                nb_tree_leaves: 0,
            });
            proofkeys.push(treekeys.get(cursor).unwrap().clone());
            break;
        }
        level += 1;
    }

    Ok(InclusionProof {
        tree: Tree {
            nodes: proofnodes,
            nb_leaves: proof_leaf_count,
        },
        keys: proofkeys,
    })
}

pub fn verify_inclusion_proof(
    leaf_key: &PublicKey,
    root_key: &PublicKey,
    proof: InclusionProof,
) -> bool {
    //check if the proof is valid
    if proof.keys.len() != proof.tree.nodes.len() {
        return false;
    }
    //check if the leaf is in the proof
    let leaf_index = proof.keys.iter().position(|x| *x == *leaf_key);
    if leaf_index.is_none() {
        return false;
    }
    //check if the root is at the end
    if proof.keys.last().unwrap() != root_key {
        return false;
    }
    let mut cursnode = proof.tree.nodes.get(leaf_index.unwrap()).unwrap();
    loop {
        let parent = cursnode.parent();
        if parent.is_none() {
            break;
        }
        let pnode = proof.tree.nodes.get(parent.unwrap() as usize).unwrap();
        let agg_key = agg_children_keys(pnode, &proof.keys);
        if agg_key.is_none() {
            return false;
        }
        if &agg_key.unwrap() != proof.keys.get(parent.unwrap() as usize).unwrap() {
            return false;
        }
        cursnode = pnode;
    }
    true
}

fn sort_pkeys(pubkeys: Vec<PublicKey>) -> Vec<PublicKey> {
    let mut keys = pubkeys;
    keys.sort_by_key(|k| k.serialize());
    keys
}

pub fn key_agg(keys: Vec<PublicKey>) -> MusigKeyAggCache {
    MusigKeyAggCache::new(&SECP, &sort_pkeys(keys))
}

fn agg_children_keys(node: &Node, treekeys: &Vec<PublicKey>) -> Option<PublicKey> {
    let children: Vec<PublicKey> = node
        .children
        .iter()
        .filter_map(|child| child.map(|index| index as usize))
        .filter_map(|index| treekeys.get(index).cloned())
        .collect();
    if children.len() == 0 {
        return None;
    }
    Some(key_agg(children).agg_pk_full())
}

// Copied here because the nodes and Node.children are private
/// The max radix of this tree is 4.
const RADIX: usize = 4;

#[derive(Debug, Clone)]
pub struct Node {
    idx: u32,
    parent: Option<u32>,
    children: [Option<u32>; RADIX],
    /// Exclusive range of leaves, allowed to revolve back to 0.
    leaves: (u32, u32),
    nb_tree_leaves: u32,
    level: u32,
}

impl Node {
    fn new_leaf(idx: usize, nb_tree_leaves: usize) -> Node {
        let idx = idx as u32;
        Node {
            idx,
            parent: None,
            children: [None; RADIX],
            leaves: (idx, (idx + 1) % nb_tree_leaves as u32),
            nb_tree_leaves: nb_tree_leaves as u32,
            level: 0,
        }
    }

    pub fn idx(&self) -> usize {
        self.idx as usize
    }

    pub fn parent(&self) -> Option<usize> {
        self.parent.map(|p| p as usize)
    }

    pub fn children(&self) -> impl Iterator<Item = usize> {
        self.children
            .clone()
            .into_iter()
            .filter_map(|c| c)
            .map(|c| c as usize)
    }

    pub fn level(&self) -> usize {
        self.level as usize
    }

    /// An iterator over all leaf indices under this node.
    pub fn leaves(&self) -> impl Iterator<Item = usize> {
        let (first, last) = self.leaves;
        let nb = self.nb_tree_leaves;
        (first..)
            .take(nb as usize)
            .map(move |e| e % nb)
            .take_while(move |e| first == last || *e != last)
            .map(|e| e as usize)
    }

    pub fn is_leaf(&self) -> bool {
        self.children.iter().all(|o| o.is_none())
    }

    pub fn is_root(&self) -> bool {
        self.parent.is_none()
    }
}

//TODO(stevenroose) consider eliminating this type in favor of straight in-line iterators
// for all nodes and for branches
/// A radix-4 tree.
#[derive(Debug, Clone)]
pub struct Tree {
    /// The nodes in the tree, starting with all the leaves
    /// and then building up towards the root.
    nodes: Vec<Node>,
    nb_leaves: usize,
}

impl Tree {
    /// Calculate the total number of nodes a tree would have
    /// for the given number of leaves.
    pub fn nb_nodes_for_leaves(nb_leaves: usize) -> usize {
        let mut ret = nb_leaves;
        let mut left = nb_leaves;
        while left > 1 {
            let radix = cmp::min(left, RADIX);
            left -= radix;
            left += 1;
            ret += 1;
        }
        ret
    }

    pub fn new(nb_leaves: usize) -> Tree {
        assert_ne!(nb_leaves, 0, "trees can't be empty");

        let mut nodes = Vec::with_capacity(Tree::nb_nodes_for_leaves(nb_leaves));

        // First we add all the leaves to the tree.
        nodes.extend((0..nb_leaves).map(|i| Node::new_leaf(i, nb_leaves)));

        let mut cursor = 0;
        // As long as there is more than 1 element on the leftover stack,
        // we have to add more nodes.
        while cursor < nodes.len() - 1 {
            let mut children = [None; RADIX];
            let mut nb_children = 0;
            let mut max_child_level = 0;
            while cursor < nodes.len() && nb_children < RADIX {
                children[nb_children] = Some(cursor as u32);

                let new_idx = nodes.len(); // idx of next node
                let child = &mut nodes[cursor];
                child.parent = Some(new_idx as u32);

                // adjust level and leaf indices
                if child.level > max_child_level {
                    max_child_level = child.level;
                }

                cursor += 1;
                nb_children += 1;
            }
            nodes.push(Node {
                idx: nodes.len() as u32,
                leaves: (
                    nodes[children.first().unwrap().unwrap() as usize].leaves.0,
                    nodes[children.iter().filter_map(|c| *c).last().unwrap() as usize]
                        .leaves
                        .1,
                ),
                children,
                level: max_child_level + 1,
                parent: None,
                nb_tree_leaves: nb_leaves as u32,
            });
        }

        Tree { nodes, nb_leaves }
    }

    pub fn nb_leaves(&self) -> usize {
        self.nb_leaves
    }

    pub fn nb_nodes(&self) -> usize {
        self.nodes.len()
    }

    pub fn root(&self) -> &Node {
        self.nodes.last().expect("no empty trees")
    }

    /// Iterate over all nodes, starting with the leaves, towards the root.
    pub fn iter(&self) -> std::slice::Iter<Node> {
        self.nodes.iter()
    }

    /// Iterate over all nodes, starting with the leaves, towards the root.
    pub fn into_iter(self) -> std::vec::IntoIter<Node> {
        self.nodes.into_iter()
    }

    /// Iterate nodes over a branch starting at the leaf
    /// with index [leaf_idx] ending in the root.
    pub fn iter_branch(&self, leaf_idx: usize) -> BranchIter {
        assert!(leaf_idx < self.nodes.len());
        BranchIter {
            tree: &self,
            cursor: Some(leaf_idx),
        }
    }

    pub fn parent_idx_of(&self, idx: usize) -> Option<usize> {
        self.nodes
            .get(idx)
            .and_then(|n| n.parent.map(|c| c as usize))
    }

    /// Returns index of the the parent of the node with given `idx`,
    /// and the index of the node among its siblings.
    pub fn parent_idx_of_with_sibling_idx(&self, idx: usize) -> Option<(usize, usize)> {
        self.nodes
            .get(idx)
            .and_then(|n| n.parent)
            .map(|parent_idx| {
                let child_idx = self.nodes[parent_idx as usize]
                    .children
                    .iter()
                    .position(|c| *c == Some(idx as u32))
                    .expect("broken tree");
                (
                    self.nodes[parent_idx as usize].idx as usize,
                    child_idx as usize,
                )
            })
    }
}

/// Iterates a tree branch.
pub struct BranchIter<'a> {
    tree: &'a Tree,
    cursor: Option<usize>,
}

impl<'a> Iterator for BranchIter<'a> {
    type Item = &'a Node;
    fn next(&mut self) -> Option<Self::Item> {
        if let Some(cursor) = self.cursor {
            let ret = &self.tree.nodes[cursor];
            self.cursor = ret.parent();
            Some(ret)
        } else {
            None
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use hex;
    use rand::{RngCore, SeedableRng};
    use secp256k1_zkp::Keypair;
    use std::time::Instant;

    #[test]

    fn test_merk_agg() {
        k_merk_agg(19);
    }
    fn k_merk_agg(keycount: u32) {
        let pubkeys = generate_test_keys(keycount, 42);
        let start = Instant::now();
        let tree = Tree::new(pubkeys.len());
        let (rootkey, treekeys) = merkelized_key_aggregation(pubkeys);
        let res = start.elapsed();
        println!("Time to generate for {} leaf-keys: {:?}", keycount, res);
        println!("Root key: {:?}", hex::encode(rootkey.serialize()));

        let rrootkey = agg_children_keys(tree.root(), &treekeys);
        println!(
            "Recovered Root key: {:?}",
            hex::encode(rrootkey.unwrap().serialize())
        );

        println!("Tree keys: {:?}", treekeys.len());
        let sample = 1;
        let sample_node = tree.nodes.get(sample).unwrap();
        let nodeky = treekeys.get(sample).unwrap().clone();
        let agged = agg_children_keys(sample_node, &treekeys);
        if agged.is_some() {
            println!("Agg key: {:?}", hex::encode(agged.unwrap().serialize()));
        }
        println!("Node key: {:?}\n", hex::encode(nodeky.serialize()));
    }

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

    #[test]
    fn test_inclusion_proof() {
        let leafcount = 1195;
        let pubkeys = generate_test_keys(leafcount, 42);
        let (rootkey, _treekeys) = merkelized_key_aggregation(pubkeys.clone());
        let key = pubkeys.get(194).unwrap().clone();

        match generate_inclusion_proof(key, pubkeys.clone()) {
            Ok(proof) => {
                println!("Proof keys: {:?}", proof.keys.len());

                let res = verify_inclusion_proof(&key, &rootkey, proof);
                println!("Proof verified: {:?}", res);
            }
            Err(msg) => {
                println!("Error: {:?}", msg);
            }
        }
    }
}
