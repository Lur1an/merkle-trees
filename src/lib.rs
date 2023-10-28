use sha3::{
    digest::{generic_array::GenericArray, Output},
    Digest, Sha3_256, Sha3_512,
};
/// Returns the index of a node in a binary tree given `depth` and `offset`.
/// # Examples
/// ```
/// # use merkle_trees::node_index;
/// let (depth, offset) = (2, 3);
/// let computed_index = node_index(depth, offset);
/// assert_eq!(computed_index, 6);
/// ```
#[inline]
pub fn node_index(depth: u32, offset: u32) -> usize {
    (1 << depth) - 1 + offset as usize
}

/// Returns the depth of a node given its index.
/// # Examples
///```
/// # use merkle_trees::node_depth;
/// let index = 14;
/// let computed_depth = node_depth(index);
/// assert_eq!(computed_depth, 3);
///```
#[inline]
pub fn node_depth(index: usize) -> u32 {
    31 - (index as u32 + 1).leading_zeros()
}

/// Returns the index to the parent node given the child node index.
///
/// # Panics
/// If the node index is 0 as that would be the root node.
///
/// # Examples
/// ```
/// # use merkle_trees::node_parent_index;
/// let index = 8;
/// let computed_parent_index = node_parent_index(index);
/// assert_eq!(computed_parent_index, 3);
/// ```
#[inline]
pub fn node_parent_index(index: usize) -> usize {
    (index - 1) / 2
}

/// Returns the left child's index given the parent node index.
/// # Examples
/// ```
/// # use merkle_trees::left_child_index;
/// let index = 6;
/// let left_child_index = left_child_index(index);
/// assert_eq!(left_child_index, 13);
/// ```
#[inline]
pub fn left_child_index(index: usize) -> usize {
    index * 2 + 1
}

#[derive(Debug)]
pub struct MerkleTree {
    depth: u32,
    nodes: Vec<Output<Sha3_256>>,
}

fn hash(v1: &[u8], v2: &[u8]) -> Output<Sha3_256> {
    let mut hasher = Sha3_256::new();
    hasher.update(v1);
    hasher.update(v2);
    hasher.finalize()
}

/// A node in a Merkle proof.
/// Contains information about the position in the tree and hash of the sibling node.
#[derive(Debug, PartialEq, Eq)]
pub enum ProofNode<'a> {
    Left(&'a [u8]),
    Right(&'a [u8]),
}

struct MerkleProof<'a> {
    node_index: usize,
    tree: &'a MerkleTree,
}

impl<'a> Iterator for MerkleProof<'a> {
    type Item = ProofNode<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.node_index == 0 {
            return None;
        }
        let proof_node = if self.node_index % 2 == 0 {
            let sibling = &self.tree.nodes[self.node_index - 1];
            ProofNode::Right(sibling)
        } else {
            let sibling = &self.tree.nodes[self.node_index + 1];
            ProofNode::Left(sibling)
        };
        self.node_index = node_parent_index(self.node_index);
        Some(proof_node)
    }
}

/// Computes the root hash of a Merkle tree given a leaf node hash and a Merkle proof for given
/// node.
pub fn verify<'a>(
    proof: impl Iterator<Item = ProofNode<'a>>,
    leaf_hash: &[u8],
) -> Output<Sha3_256> {
    let mut computed_hash = *GenericArray::from_slice(leaf_hash);
    for p_node in proof {
        match p_node {
            ProofNode::Left(sibling) => {
                computed_hash = hash(&computed_hash, sibling);
            }
            ProofNode::Right(sibling) => {
                computed_hash = hash(sibling, &computed_hash);
            }
        }
    }
    computed_hash
}

impl MerkleTree {
    /// Creates a new Merkle tree with the given depth and initial leaf hash.
    /// # Arguments
    /// * `depth` - The depth of the tree. Max depth is 30, counted from 0.
    /// * `initial_leaf_hash` - The `Sha3_256` hash of the initial leaf node.
    ///
    /// # Panics
    /// If `depth > 30`
    pub fn new(depth: u32, initial_leaf_hash: &[u8]) -> Self {
        assert!(depth <= 30);
        let mut computed_hash = *GenericArray::from_slice(initial_leaf_hash);
        let mut nodes = vec![computed_hash; (1 << depth + 1) - 1];
        for layer in (0..depth).rev() {
            let new_hash = hash(&computed_hash, &computed_hash);
            for offset in 0..(1 << layer) {
                nodes[node_index(layer, offset)] = new_hash;
            }
            computed_hash = new_hash;
        }
        Self { depth, nodes }
    }

    #[inline]
    pub fn root(&self) -> &Output<Sha3_256> {
        &self.nodes[0]
    }

    #[inline]
    pub fn num_leaves(&self) -> u32 {
        1 << self.depth
    }

    /// Returns an iterator over the Merkle proof nodes for a given leaf node.
    /// # Arguments
    /// * `leaf_offset` - Index to the *leaf_node* counting from left to right starting from 0
    ///
    /// # Panics
    /// If `leaf_offset > 2^(depth) - 1` as that offset would be invalid.
    pub fn proof<'a>(&'a self, leaf_offset: u32) -> impl Iterator<Item = ProofNode<'a>> {
        assert!(leaf_offset < self.num_leaves());
        MerkleProof {
            node_index: node_index(self.depth, leaf_offset),
            tree: self,
        }
    }

    /// # Arguments
    /// * `leaf_offset` - Index to the *leaf_node* counting from left to right starting from 0
    /// * `leaf_hash` - The `Sha3_256` hash of the leaf node.
    ///
    /// # Panics
    /// If `leaf_offset > 2^(depth) - 1` as that offset would be invalid.
    pub fn set(&mut self, leaf_offset: u32, leaf_hash: &[u8]) {
        assert!(leaf_offset < self.num_leaves());
        let leaf_index = node_index(self.depth, leaf_offset);
        self.nodes[leaf_index] = *GenericArray::from_slice(leaf_hash);
        let mut updated_node = leaf_index;
        while updated_node != 0 {
            let parent = node_parent_index(updated_node);
            let l_child = left_child_index(parent);
            let r_child = l_child + 1;
            self.nodes[parent] = hash(&self.nodes[l_child], &self.nodes[r_child]);
            updated_node = parent;
        }
    }
}

#[cfg(test)]
mod test {
    use hex_literal::hex;

    use super::*;

    #[test]
    fn merkle_tree_initialization() {
        let initial_leaf_hash =
            hex!("abababababababababababababababababababababababababababababababab");
        {
            let tree = MerkleTree::new(0, &initial_leaf_hash);
            let expected_root_hash = &initial_leaf_hash;
            assert_eq!(tree.root()[..], expected_root_hash[..]);
        }
        {
            let tree = MerkleTree::new(19, &initial_leaf_hash);
            let expected_root_hash =
                hex!("d4490f4d374ca8a44685fe9471c5b8dbe58cdffd13d30d9aba15dd29efb92930");
            assert_eq!(tree.root()[..], expected_root_hash[..]);
        }
    }

    #[test]
    fn merkle_tree_update() {
        let initial_leaf_hash =
            hex!("abababababababababababababababababababababababababababababababab");
        let mut tree = MerkleTree::new(16, &initial_leaf_hash);
        let leaf_hash_update =
            hex!("d4490f4d374ca8a44685fe9471c5b8dbe58cdffd13d30d9aba15dd29efb92930");
        tree.set(69, &leaf_hash_update);
        let expected_root_hash =
            hex!("9e098604876e9a6a0041c2ee01ffe1a7a591dc65f3e00033146f2c655491d0dc");
        assert_eq!(tree.root()[..], expected_root_hash[..]);
    }

    /// Helper function to achieve the 256bit multiplication from the example
    fn multiply(x: u64, y: &[u8; 32]) -> [u8; 32] {
        let mut result = [0u8; 32];
        let mut carry = 0u64;

        for i in (0..32).rev() {
            let product = x * (y[i] as u64) + carry;
            result[i] = product as u8; // store the lowest 8 bits
            carry = product >> 8; // carry the remaining bits
        }
        result
    }

    const TEST_HEX: [u8; 32] =
        hex!("1111111111111111111111111111111111111111111111111111111111111111");

    #[test]
    fn merkle_tree_proof() {
        let initial_leaf_hash =
            hex!("0000000000000000000000000000000000000000000000000000000000000000");
        let mut tree = MerkleTree::new(4, &initial_leaf_hash);
        for i in 0..tree.num_leaves() {
            tree.set(i, &multiply(i.into(), &TEST_HEX));
        }
        let expected_root_hash =
            hex!("57054e43fa56333fd51343b09460d48b9204999c376624f52480c5593b91eff4");
        assert_eq!(tree.root()[..], expected_root_hash[..]);
        let proof = tree.proof(3).collect::<Vec<_>>();
        let expected_proof = [
            ProofNode::Right(&hex!(
                "2222222222222222222222222222222222222222222222222222222222222222"
            )),
            ProofNode::Right(&hex!(
                "35e794f1b42c224a8e390ce37e141a8d74aa53e151c1d1b9a03f88c65adb9e10"
            )),
            ProofNode::Left(&hex!(
                "26fca7737f48fa702664c8b468e34c858e62f51762386bd0bddaa7050e0dd7c0"
            )),
            ProofNode::Left(&hex!(
                "e7e11a86a0c1d8d8624b1629cb58e39bb4d0364cb8cb33c4029662ab30336858"
            )),
        ];
        assert_eq!(proof, expected_proof);
    }

    #[test]
    fn merkle_proof_verify() {
        let initial_leaf_hash =
            hex!("0000000000000000000000000000000000000000000000000000000000000000");
        let mut tree = MerkleTree::new(4, &initial_leaf_hash);
        for i in 0..tree.num_leaves() {
            tree.set(i, &multiply(i.into(), &TEST_HEX));
        }
        let leaf_5 = multiply(5, &TEST_HEX);
        let root = tree.root();
        let proof = tree.proof(5);
        assert_eq!(verify(proof, &leaf_5)[..], root[..]);
    }
}
