//! Salted BLAKE3 Merkle trees whose leaves are cosets {x : x^(2^g) = y} with merged openings (Section 3.4, "Salted Merkle
//! commitments"), and the Fiat-Shamir transcript with the challenge maps phi and pos of
//! Section 7.4.
//!
//! Leaves are H_{K0}(values || salt), internal nodes H_{K1}(left || right), with BLAKE3 in keyed
//! mode under two fixed keys K0 = 0^32, K1 = 1^32 (domain separation). With `salt_len = 0` the
//! trees are unsalted (used only to measure the cost of salting).

use crate::field::{ExtField, Field, Fp, P};

pub type Digest = [u8; 32];

const LEAF_KEY: [u8; 32] = [0u8; 32];
const NODE_KEY: [u8; 32] = [1u8; 32];

fn hash_leaf<F: Field>(vals: &[F], salt: &[u8]) -> Digest {
    let mut buf = Vec::with_capacity(8 * 4 * vals.len() + salt.len());
    for v in vals {
        v.to_bytes(&mut buf);
    }
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

/// Salted Merkle tree over the cosets of a word w on L_j under x -> x^(2^g): with T = |w| / 2^g
/// leaves, leaf t holds `w[t + u T]` for u = 0 .. 2^g - 1 (the 2^g points whose 2^g-th power is
/// the point t of L_{j+g}). For g = 1 the leaves are the fibres {x, -x}.
pub struct MerkleTree {
    /// layers[0] = leaf hashes, last layer = [root]
    layers: Vec<Vec<Digest>>,
    salts: Vec<u8>,
    salt_len: usize,
}

/// The values of leaf t of the coset tree of `w` with group size 2^g.
pub fn leaf_values<F: Field>(w: &[F], g: usize, t: usize) -> Vec<F> {
    let leaves = w.len() >> g;
    (0..1usize << g).map(|u| w[t + u * leaves]).collect()
}

/// Leaf `lambda` of the fibre tree of `w` in coset order for group size 2^g: the fibre
/// `(w[f], w[f + |w|/2])` with `f = t + u |w|/2^g`, where `lambda = t 2^(g-1) + u`, `u < 2^(g-1)`.
/// The 2^(g-1) fibres of the coset t (the points whose 2^g-th power is point t of L_g) are the
/// consecutive leaves t 2^(g-1) .. (t+1) 2^(g-1) - 1. For g = 1 leaf f is the fibre f.
pub fn fibre_leaf<F: Field>(w: &[F], g: usize, lambda: usize) -> Vec<F> {
    let (t, u) = (lambda >> (g - 1), lambda & ((1 << (g - 1)) - 1));
    let f = t + u * (w.len() >> g);
    vec![w[f], w[f + w.len() / 2]]
}

impl MerkleTree {
    /// Tree of the word `w` with group size 2^g (at least 2 leaves), salts from the stream of
    /// `seed` on `label`.
    pub fn new<F: Field>(w: &[F], g: usize, seed: &Digest, label: &[u8], salt_len: usize) -> Self {
        let leaves = w.len() >> g;
        assert!(g >= 1 && leaves >= 1 && leaves.is_power_of_two() && leaves << g == w.len());
        Self::build(leaves, |t| leaf_values(w, g, t), seed, label, salt_len)
    }
    /// Tree of the fibres of `w`, in the coset order of [`fibre_leaf`] for group size 2^g.
    pub fn new_fibres<F: Field>(
        w: &[F],
        g: usize,
        seed: &Digest,
        label: &[u8],
        salt_len: usize,
    ) -> Self {
        let leaves = w.len() / 2;
        assert!(g >= 1 && leaves.is_power_of_two() && w.len() >> g >= 1);
        Self::build(leaves, |l| fibre_leaf(w, g, l), seed, label, salt_len)
    }
    fn build<F: Field>(
        leaves: usize,
        leaf: impl Fn(usize) -> Vec<F> + Sync + Send,
        seed: &Digest,
        label: &[u8],
        salt_len: usize,
    ) -> Self {
        let mut salts = vec![0u8; leaves * salt_len];
        if salt_len > 0 {
            salt_stream(seed, label).fill(&mut salts);
        }
        let hashes: Vec<Digest> = crate::par::map_range(leaves, |t| {
            hash_leaf(&leaf(t), &salts[t * salt_len..(t + 1) * salt_len])
        });
        let mut layers = vec![hashes];
        while layers.last().unwrap().len() > 1 {
            let prev = layers.last().unwrap();
            let next: Vec<Digest> = crate::par::map_range(prev.len() / 2, |i| {
                hash_node(&prev[2 * i], &prev[2 * i + 1])
            });
            layers.push(next);
        }
        MerkleTree {
            layers,
            salts,
            salt_len,
        }
    }
    pub fn root(&self) -> Digest {
        self.layers.last().unwrap()[0]
    }
    /// Depth of the tree.
    pub fn depth(&self) -> usize {
        self.layers.len() - 1
    }
    /// Salt of leaf `t`.
    pub fn salt(&self, t: usize) -> Vec<u8> {
        self.salts[t * self.salt_len..(t + 1) * self.salt_len].to_vec()
    }
    /// Merged authentication paths of the leaves `positions` (strictly increasing): the nodes
    /// that cannot be recomputed from the opened leaves, level by level from the leaves up, each
    /// level from left to right (the order in which [`verify_multi`] consumes them).
    pub fn multi_path(&self, positions: &[usize]) -> Vec<Digest> {
        let mut nodes = Vec::new();
        let mut cur: Vec<usize> = positions.to_vec();
        for layer in &self.layers[..self.layers.len() - 1] {
            let mut next = Vec::with_capacity(cur.len());
            let mut i = 0;
            while i < cur.len() {
                let p = cur[i];
                if i + 1 < cur.len() && cur[i + 1] == p ^ 1 {
                    i += 2;
                } else {
                    nodes.push(layer[p ^ 1]);
                    i += 1;
                }
                next.push(p >> 1);
            }
            cur = next;
        }
        nodes
    }
}

/// Checks merged openings against `root` for a tree of depth `depth`: `leaves` are the opened
/// leaves (position, values, salt) with strictly increasing positions below 2^depth, and `nodes`
/// the merged paths in the order of [`MerkleTree::multi_path`]. Every node must be used.
pub fn verify_multi<F: Field>(
    root: &Digest,
    depth: usize,
    leaves: &[(usize, &[F], &[u8])],
    nodes: &[Digest],
) -> bool {
    if leaves.is_empty() || depth >= usize::BITS as usize {
        return false;
    }
    if leaves.windows(2).any(|w| w[0].0 >= w[1].0) || leaves.last().unwrap().0 >> depth != 0 {
        return false;
    }
    let mut cur: Vec<(usize, Digest)> = leaves
        .iter()
        .map(|&(p, v, s)| (p, hash_leaf(v, s)))
        .collect();
    let mut k = 0;
    for _ in 0..depth {
        let mut next = Vec::with_capacity(cur.len());
        let mut i = 0;
        while i < cur.len() {
            let (p, h) = cur[i];
            let parent = if i + 1 < cur.len() && cur[i + 1].0 == p ^ 1 {
                i += 2;
                hash_node(&h, &cur[i - 1].1)
            } else {
                let Some(sib) = nodes.get(k) else {
                    return false;
                };
                k += 1;
                i += 1;
                if p & 1 == 0 {
                    hash_node(&h, sib)
                } else {
                    hash_node(sib, &h)
                }
            };
            next.push((p >> 1, parent));
        }
        cur = next;
    }
    k == nodes.len() && cur.len() == 1 && cur[0].1 == *root
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
        Transcript {
            state: *blake3::hash(label).as_bytes(),
            counter: 0,
        }
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
        let mut x: Vec<u64> = bytes
            .chunks_exact(8)
            .map(|c| u64::from_le_bytes(c.try_into().unwrap()))
            .collect();
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
    fn multi_openings() {
        let w: Vec<Fp> = (0..256u64).map(Fp::new).collect();
        for g in [1, 2, 4] {
            for salt_len in [0, 32] {
                let t = MerkleTree::new(&w, g, &[7u8; 32], b"t", salt_len);
                let leaves = 256 >> g;
                for pos in [
                    vec![0],
                    vec![3, 4],
                    vec![0, 1, 2, 3],
                    vec![1, 5, 6, leaves - 1],
                ] {
                    let vals: Vec<Vec<Fp>> = pos.iter().map(|&p| leaf_values(&w, g, p)).collect();
                    let salts: Vec<Vec<u8>> = pos.iter().map(|&p| t.salt(p)).collect();
                    let open: Vec<(usize, &[Fp], &[u8])> = pos
                        .iter()
                        .enumerate()
                        .map(|(i, &p)| (p, vals[i].as_slice(), salts[i].as_slice()))
                        .collect();
                    let nodes = t.multi_path(&pos);
                    assert!(verify_multi(&t.root(), t.depth(), &open, &nodes));
                    // extra, missing or changed nodes, a wrong depth, changed values are rejected
                    let mut more = nodes.clone();
                    more.push([0u8; 32]);
                    assert!(!verify_multi(&t.root(), t.depth(), &open, &more));
                    if !nodes.is_empty() {
                        assert!(!verify_multi(&t.root(), t.depth(), &open, &nodes[1..]));
                        let mut bad = nodes.clone();
                        bad[0][0] ^= 1;
                        assert!(!verify_multi(&t.root(), t.depth(), &open, &bad));
                    }
                    assert!(!verify_multi(&t.root(), t.depth() + 1, &open, &nodes));
                    let mut v2 = vals[0].clone();
                    v2[0] = v2[0] + Fp::ONE;
                    let mut open2 = open.clone();
                    open2[0].1 = &v2;
                    assert!(!verify_multi(&t.root(), t.depth(), &open2, &nodes));
                }
            }
        }
        // the salts depend on the seed
        let a = MerkleTree::new(&w, 1, &[1u8; 32], b"t", 32);
        let b = MerkleTree::new(&w, 1, &[2u8; 32], b"t", 32);
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
