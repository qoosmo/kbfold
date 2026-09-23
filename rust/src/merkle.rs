//! BLAKE3 Merkle trees whose leaves are fibres {x, -x}, and a Fiat-Shamir transcript.

use crate::field::{Field, Fp, Fp2, P};

pub type Digest = [u8; 32];

fn hash_leaf<F: Field>(a: &F, b: &F) -> Digest {
    let mut buf = Vec::with_capacity(32);
    a.to_bytes(&mut buf);
    b.to_bytes(&mut buf);
    let mut h = blake3::Hasher::new();
    h.update(&[0u8]); // leaf domain separator
    h.update(&buf);
    *h.finalize().as_bytes()
}

fn hash_node(l: &Digest, r: &Digest) -> Digest {
    let mut h = blake3::Hasher::new();
    h.update(&[1u8]); // node domain separator
    h.update(l);
    h.update(r);
    *h.finalize().as_bytes()
}

/// Merkle tree over the fibres of a word w on L_j: leaf i = (w[i], w[i + n/2]).
pub struct MerkleTree {
    /// layers[0] = leaf hashes, last layer = [root]
    layers: Vec<Vec<Digest>>,
}

impl MerkleTree {
    pub fn new<F: Field>(w: &[F]) -> Self {
        let h = w.len() / 2;
        assert!(h.is_power_of_two());
        let leaves: Vec<Digest> = (0..h).map(|i| hash_leaf(&w[i], &w[i + h])).collect();
        let mut layers = vec![leaves];
        while layers.last().unwrap().len() > 1 {
            let prev = layers.last().unwrap();
            let next: Vec<Digest> = prev.chunks_exact(2).map(|c| hash_node(&c[0], &c[1])).collect();
            layers.push(next);
        }
        MerkleTree { layers }
    }
    pub fn root(&self) -> Digest {
        self.layers.last().unwrap()[0]
    }
    pub fn path(&self, mut i: usize) -> Vec<Digest> {
        let mut p = Vec::with_capacity(self.layers.len() - 1);
        for layer in &self.layers[..self.layers.len() - 1] {
            p.push(layer[i ^ 1]);
            i >>= 1;
        }
        p
    }
}

pub fn verify_path<F: Field>(root: &Digest, i: usize, a: &F, b: &F, path: &[Digest]) -> bool {
    let mut cur = hash_leaf(a, b);
    let mut idx = i;
    for sib in path {
        cur = if idx & 1 == 0 { hash_node(&cur, sib) } else { hash_node(sib, &cur) };
        idx >>= 1;
    }
    idx == 0 && &cur == root
}

/// Hash-chain transcript: state_{k+1} = BLAKE3(state_k || tag || data).
pub struct Transcript {
    state: Digest,
    counter: u64,
}

impl Transcript {
    pub fn new(label: &[u8]) -> Self {
        Transcript { state: *blake3::hash(label).as_bytes(), counter: 0 }
    }
    pub fn absorb_bytes(&mut self, tag: &[u8], data: &[u8]) {
        let mut h = blake3::Hasher::new();
        h.update(&self.state);
        h.update(tag);
        h.update(&(data.len() as u64).to_le_bytes());
        h.update(data);
        self.state = *h.finalize().as_bytes();
        self.counter = 0;
    }
    pub fn absorb_field<F: Field>(&mut self, tag: &[u8], xs: &[F]) {
        let mut buf = Vec::new();
        for x in xs {
            x.to_bytes(&mut buf);
        }
        self.absorb_bytes(tag, &buf);
    }
    fn squeeze(&mut self) -> Digest {
        let mut h = blake3::Hasher::new();
        h.update(&self.state);
        h.update(b"squeeze");
        h.update(&self.counter.to_le_bytes());
        self.counter += 1;
        *h.finalize().as_bytes()
    }
    fn fp_from(bytes: &[u8]) -> Fp {
        // 128-bit value reduced mod p: statistical distance from uniform < 2^-64
        let x = u128::from_le_bytes(bytes[..16].try_into().unwrap());
        Fp((x % P as u128) as u64)
    }
    pub fn challenge_ext(&mut self) -> Fp2 {
        let d = self.squeeze();
        Fp2(Self::fp_from(&d[..16]), Self::fp_from(&d[16..]))
    }
    pub fn challenge_index(&mut self, n: usize) -> usize {
        assert!(n.is_power_of_two());
        let d = self.squeeze();
        (u64::from_le_bytes(d[..8].try_into().unwrap()) as usize) & (n - 1)
    }
}
