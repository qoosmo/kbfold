//! Salted BLAKE3 Merkle trees whose leaves are fibres {x, -x} (Section 3.4, "Salted Merkle
//! commitments"), and the Fiat-Shamir transcript with the challenge maps phi and pos of
//! Section 7.4.
//!
//! Leaves are H_{K0}(a || b || salt), internal nodes H_{K1}(left || right), with BLAKE3 in keyed
//! mode under two fixed keys K0 = 0^32, K1 = 1^32 (domain separation). With `salt_len = 0` the
//! trees are unsalted (used only to measure the cost of salting).

use crate::field::{ExtField, Field, Fp, P};

pub type Digest = [u8; 32];

const LEAF_KEY: [u8; 32] = [0u8; 32];
const NODE_KEY: [u8; 32] = [1u8; 32];

fn hash_leaf<F: Field>(a: &F, b: &F, salt: &[u8]) -> Digest {
    let mut buf = Vec::with_capacity(64 + salt.len());
    a.to_bytes(&mut buf);
    b.to_bytes(&mut buf);
    let mut h = blake3::Hasher::new_keyed(&LEAF_KEY);
    h.update(&buf);
    h.update(salt);
    *h.finalize().as_bytes()
}

fn hash_node(l: &Digest, r: &Digest) -> Digest {
    let mut h = blake3::Hasher::new_keyed(&NODE_KEY);
    h.update(l);
    h.update(r);
    *h.finalize().as_bytes()
}

/// The salt stream of one tree: the extendable output of BLAKE3 keyed with the prover seed on the
/// tree label; leaf i gets the bytes [i len, (i+1) len). The seed must be fresh and secret.
fn salt_stream(seed: &Digest, label: &[u8]) -> blake3::OutputReader {
    let mut h = blake3::Hasher::new_keyed(seed);
    h.update(b"kbfold/v0.3/leaf-salts");
    h.update(&(label.len() as u64).to_le_bytes());
    h.update(label);
    h.finalize_xof()
}

/// Salted Merkle tree over the fibres of a word w on L_j: leaf i = `(w[i], w[i + n/2])`.
pub struct MerkleTree {
    /// layers[0] = leaf hashes, last layer = [root]
    layers: Vec<Vec<Digest>>,
    salts: Vec<u8>,
    salt_len: usize,
}

impl MerkleTree {
    /// Tree of the word `w` (length a power of 2, at least 2), with the salts of the stream of
    /// `seed` on `label`.
    pub fn new<F: Field>(w: &[F], seed: &Digest, label: &[u8], salt_len: usize) -> Self {
        let h = w.len() / 2;
        assert!(h.is_power_of_two() && w.len() == 2 * h);
        let mut salts = vec![0u8; h * salt_len];
        if salt_len > 0 {
            salt_stream(seed, label).fill(&mut salts);
        }
        let leaves: Vec<Digest> = (0..h)
            .map(|i| hash_leaf(&w[i], &w[i + h], &salts[i * salt_len..(i + 1) * salt_len]))
            .collect();
        let mut layers = vec![leaves];
        while layers.last().unwrap().len() > 1 {
            let prev = layers.last().unwrap();
            let next: Vec<Digest> = prev.chunks_exact(2).map(|c| hash_node(&c[0], &c[1])).collect();
            layers.push(next);
        }
        MerkleTree { layers, salts, salt_len }
    }
    pub fn root(&self) -> Digest {
        self.layers.last().unwrap()[0]
    }
    /// Depth of the tree: the length of every authentication path.
    pub fn depth(&self) -> usize {
        self.layers.len() - 1
    }
    /// Authentication path of leaf `i` (siblings from the leaves to the root).
    pub fn path(&self, mut i: usize) -> Vec<Digest> {
        let mut p = Vec::with_capacity(self.depth());
        for layer in &self.layers[..self.layers.len() - 1] {
            p.push(layer[i ^ 1]);
            i >>= 1;
        }
        p
    }
    /// Salt of leaf `i`.
    pub fn salt(&self, i: usize) -> Vec<u8> {
        self.salts[i * self.salt_len..(i + 1) * self.salt_len].to_vec()
    }
}

/// Checks the opening `(a, b, salt, path)` of leaf `i` of a tree of depth `depth` against `root`.
/// Returns `false` on any length mismatch.
pub fn verify_path<F: Field>(
    root: &Digest,
    depth: usize,
    i: usize,
    a: &F,
    b: &F,
    salt: &[u8],
    path: &[Digest],
) -> bool {
    if path.len() != depth || (depth < usize::BITS as usize && i >> depth != 0) {
        return false;
    }
    let mut cur = hash_leaf(a, b, salt);
    let mut idx = i;
    for sib in path {
        cur = if idx & 1 == 0 { hash_node(&cur, sib) } else { hash_node(sib, &cur) };
        idx >>= 1;
    }
    &cur == root
}

/// Hash-chain transcript: state_{k+1} = H(state_k || tag || len || data); outputs are
/// H(state || "squeeze" || counter).
#[derive(Clone)]
pub struct Transcript {
    state: Digest,
    counter: u64,
}

impl Transcript {
    pub fn new(label: &[u8]) -> Self {
        Transcript { state: *blake3::hash(label).as_bytes(), counter: 0 }
    }
    pub fn absorb(&mut self, tag: &[u8], data: &[u8]) {
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
        self.absorb(tag, &buf);
    }
    /// `len` pseudorandom bytes.
    pub fn squeeze(&mut self, len: usize) -> Vec<u8> {
        let mut h = blake3::Hasher::new();
        h.update(&self.state);
        h.update(b"squeeze");
        h.update(&self.counter.to_le_bytes());
        self.counter += 1;
        let mut out = vec![0u8; len];
        h.finalize_xof().fill(&mut out);
        out
    }
    /// Challenge in F = F_{p^e} by the map phi of Section 7.4 from beta = 64(e+1) bits: the
    /// integer int(vr) is reduced mod p^e, and its base-p digits are the coordinates.
    pub fn challenge<E: ExtField>(&mut self) -> E {
        let bytes = self.squeeze(8 * (E::DEGREE + 1));
        let mut x: Vec<u64> =
            bytes.chunks_exact(8).map(|c| u64::from_le_bytes(c.try_into().unwrap())).collect();
        let mut digits = Vec::with_capacity(E::DEGREE);
        for _ in 0..E::DEGREE {
            // x <- floor(x / p), digit = x mod p (long division, most significant limb first)
            let mut rem: u128 = 0;
            for limb in x.iter_mut().rev() {
                let cur = (rem << 64) | *limb as u128;
                *limb = (cur / P as u128) as u64;
                rem = cur % P as u128;
            }
            digits.push(Fp(rem as u64));
        }
        E::from_digits(&digits)
    }
    /// `kappa` query indices in [0, 2^bits), from `kappa * bits` consecutive output bits (map pos).
    pub fn query_indices(&mut self, kappa: usize, bits: usize) -> Vec<usize> {
        let bytes = self.squeeze((kappa * bits).div_ceil(8));
        (0..kappa)
            .map(|q| {
                let mut idx = 0usize;
                for b in 0..bits {
                    let pos = q * bits + b;
                    idx |= (((bytes[pos / 8] >> (pos % 8)) & 1) as usize) << b;
                }
                idx
            })
            .collect()
    }
}

/// Number of challenge bits beta used by [`Transcript::challenge`] for F_{p^e}.
pub fn beta(degree: usize) -> usize {
    64 * (degree + 1)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::field::{Fp2, Fp4};

    #[test]
    fn paths_and_salts() {
        let w: Vec<Fp> = (0..64u64).map(Fp::new).collect();
        for salt_len in [0, 32] {
            let t = MerkleTree::new(&w, &[7u8; 32], b"t", salt_len);
            for i in 0..32 {
                let s = t.salt(i);
                assert_eq!(s.len(), salt_len);
                assert!(verify_path(&t.root(), t.depth(), i, &w[i], &w[i + 32], &s, &t.path(i)));
                assert!(!verify_path(&t.root(), t.depth(), i, &w[i], &w[i], &s, &t.path(i)));
                assert!(!verify_path(&t.root(), t.depth(), i ^ 1, &w[i], &w[i + 32], &s, &t.path(i)));
                assert!(!verify_path(&t.root(), t.depth() + 1, i, &w[i], &w[i + 32], &s, &t.path(i)));
                if salt_len > 0 {
                    let mut bad = s.clone();
                    bad[0] ^= 1;
                    assert!(!verify_path(&t.root(), t.depth(), i, &w[i], &w[i + 32], &bad, &t.path(i)));
                }
            }
        }
        // the salts depend on the seed
        let a = MerkleTree::new(&w, &[1u8; 32], b"t", 32);
        let b = MerkleTree::new(&w, &[2u8; 32], b"t", 32);
        assert_ne!(a.root(), b.root());
    }

    #[test]
    fn challenge_map_digits() {
        // phi reads 64(e+1) bits as an integer and takes its first e base-p digits
        let mut tr = Transcript::new(b"t");
        let mut copy = tr.clone();
        let c: Fp4 = tr.challenge();
        let bytes = copy.squeeze(40);
        let mut x = num_bigint::BigUint::from_bytes_le(&bytes);
        let p = num_bigint::BigUint::from(P);
        let mut d = Vec::new();
        for _ in 0..4 {
            let r = &x % &p;
            d.push(Fp(r.iter_u64_digits().next().unwrap_or(0)));
            x /= &p;
        }
        assert_eq!(c, Fp4::from_digits(&d));
        let c2: Fp2 = Transcript::new(b"u").challenge();
        assert_ne!(c2, Fp2::ZERO);
        assert_eq!(beta(2), 192);
        assert_eq!(beta(4), 320);
    }
}
