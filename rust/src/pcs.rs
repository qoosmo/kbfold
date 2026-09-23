//! The evaluation protocol Pi_eval of Section 5, compiled with BLAKE3 Merkle trees and Fiat-Shamir.
//!
//! Tables live over the base field F_p (Goldilocks); challenges, evaluation points and all folded
//! words live over the quadratic extension F_{p^2} (Remark 6.8, "Challenges from an extension field").

use crate::field::{Field, Fp, Fp2};
use crate::merkle::{verify_path, Digest, MerkleTree, Transcript};
use crate::poly::{eq_table, horner, kernel_to_mono, mle_eval, mobius, ntt, restrict};

/// Encoding of the table.  `Kernel` is the scheme of the paper (U = sum_b f(b) K_b, kernel fold).
/// `Monomial` is the coefficient-form baseline (U = Kronecker embedding of the monomial
/// coefficients of f~, classical FRI fold U_e + T U_o), used for comparison in Section 8.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Basis {
    Kernel,
    Monomial,
}

#[derive(Clone, Copy, Debug)]
pub struct Params {
    /// table encoding
    pub basis: Basis,
    /// number of variables m (N = 2^m)
    pub m: usize,
    /// R with rate rho = 2^-R
    pub log_inv_rate: usize,
    /// number of folding rounds s, 0 <= s <= m
    pub s: usize,
    /// number of queries kappa
    pub queries: usize,
}

impl Params {
    pub fn n(&self) -> usize {
        1 << (self.m + self.log_inv_rate)
    }
    fn omega(&self) -> Fp {
        Fp::two_adic_root((self.m + self.log_inv_rate) as u32)
    }
    fn check(&self) {
        assert!(self.s <= self.m);
        assert!(self.log_inv_rate >= 1);
        assert!(self.m + self.log_inv_rate <= 32);
        assert!(self.queries >= 1);
    }
}

pub struct ProverData {
    table: Vec<Fp>,
    w0: Vec<Fp>,
    tree0: MerkleTree,
}

#[derive(Clone, Debug)]
pub struct Opening<F> {
    pub a: F, // w_j(x)
    pub b: F, // w_j(-x)
    pub path: Vec<Digest>,
}

#[derive(Clone, Debug)]
pub struct QueryProof {
    pub level0: Opening<Fp>,
    pub levels: Vec<Opening<Fp2>>, // levels 1 .. s-1
}

#[derive(Clone, Debug)]
pub struct Proof {
    pub sumcheck: Vec<[Fp2; 3]>,
    pub roots: Vec<Digest>, // roots of w_1 .. w_{s-1}
    pub g: Vec<Fp2>,
    pub queries: Vec<QueryProof>,
}

impl Proof {
    /// Serialized size in bytes (8 bytes per F_p element, 16 per F_{p^2} element, 32 per digest).
    pub fn size_bytes(&self) -> usize {
        let mut s = self.sumcheck.len() * 3 * 16 + self.roots.len() * 32 + self.g.len() * 16;
        for q in &self.queries {
            s += 16 + 32 * q.level0.path.len();
            for o in &q.levels {
                s += 32 + 32 * o.path.len();
            }
        }
        s
    }
}

/// Enc(f): kernel -> monomial transform ((m/2)N additions), zero-pad, NTT of size n.
pub fn commit(p: &Params, table: &[Fp]) -> (Digest, ProverData) {
    p.check();
    assert_eq!(table.len(), 1 << p.m);
    let mut w0 = table.to_vec();
    to_coefficients(p.basis, &mut w0);
    w0.resize(p.n(), Fp::ZERO);
    ntt(&mut w0, p.omega());
    let tree0 = MerkleTree::new(&w0);
    let root = tree0.root();
    (root, ProverData { table: table.to_vec(), w0, tree0 })
}

/// Table -> monomial coefficients of the committed polynomial U.
pub fn to_coefficients<F: Field>(basis: Basis, v: &mut [F]) {
    match basis {
        Basis::Kernel => kernel_to_mono(v),
        Basis::Monomial => mobius(v),
    }
}

/// Kernel fold (Definition 4.5) in line form (Lemma 4.8):
///   fold_T(w)(x^2) = u + T v,  u = w_o - w_e,  v = 2 w_e - w_o,
///   w_e = (a+b)/2, w_o = (a-b)/(2x), a = w(x), b = w(-x).
/// Monomial baseline: classical FRI fold w_e + T w_o.
#[inline(always)]
fn fold_pair(basis: Basis, a: Fp2, b: Fp2, inv_2x: Fp, t: Fp2, inv2: Fp) -> Fp2 {
    let we = (a + b) * inv2;
    let wo = (a - b) * inv_2x;
    match basis {
        Basis::Kernel => (wo - we) + t * (we.double() - wo),
        Basis::Monomial => we + t * wo,
    }
}

/// Fold a whole word on L_j (size nj) to L_{j+1}.  inv_x0[k] = omega^{-k} for k < n/2 (level-0 table).
fn fold_word<F: Field + Into<Fp2>>(basis: Basis, w: &[F], t: Fp2, inv_x0: &[Fp], level: usize, inv2: Fp) -> Vec<Fp2> {
    let h = w.len() / 2;
    (0..h)
        .map(|i| {
            let inv_2x = inv_x0[i << level] * inv2;
            fold_pair(basis, w[i].into(), w[i + h].into(), inv_2x, t, inv2)
        })
        .collect()
}

fn eq1(a: Fp2, c: Fp2) -> Fp2 {
    a * c + (Fp2::ONE - a) * (Fp2::ONE - c)
}

/// h(T) from h(0), h(1), h(2).
fn interp3(h: &[Fp2; 3], t: Fp2) -> Fp2 {
    let one = Fp2::ONE;
    let two = one.double();
    let inv2: Fp2 = Fp::new(2).inv().into();
    let l0 = (t - one) * (t - two) * inv2;
    let l1 = -(t * (t - two));
    let l2 = t * (t - one) * inv2;
    l0 * h[0] + l1 * h[1] + l2 * h[2]
}

fn init_transcript(p: &Params, root: &Digest, z: &[Fp2], v: Fp2) -> Transcript {
    let mut tr = Transcript::new(b"kbfold-pcs-v1");
    let params = [p.m as u64, p.log_inv_rate as u64, p.s as u64, p.queries as u64, (p.basis == Basis::Kernel) as u64];
    let pb: Vec<u8> = params.iter().flat_map(|x| x.to_le_bytes()).collect();
    tr.absorb_bytes(b"params", &pb);
    tr.absorb_bytes(b"root0", root);
    tr.absorb_field(b"point", z);
    tr.absorb_field(b"value", &[v]);
    tr
}

/// Prover: returns the value v = f~(z) and the proof.
pub fn open(p: &Params, pd: &ProverData, z: &[Fp2]) -> (Fp2, Proof) {
    open_inner(p, pd, z, None)
}

/// `cheat = Some(d)`: claim v + d instead of v, shift h_0 so that the first sumcheck check passes,
/// fold honestly, and adjust the final table so that the closure check passes (used in tests).
fn open_inner(p: &Params, pd: &ProverData, z: &[Fp2], cheat: Option<Fp2>) -> (Fp2, Proof) {
    p.check();
    assert_eq!(z.len(), p.m);
    let n = p.n();
    let inv2 = Fp::new(2).inv();
    let omega_inv = p.omega().inv();
    let mut inv_x0 = Vec::with_capacity(n / 2);
    let mut acc = Fp::ONE;
    for _ in 0..n / 2 {
        inv_x0.push(acc);
        acc = acc * omega_inv;
    }

    let mut a: Vec<Fp2> = pd.table.iter().map(|&x| x.into()).collect();
    let mut e = eq_table(z);
    let mut v = a.iter().zip(&e).fold(Fp2::ZERO, |s, (&x, &y)| s + x * y);
    if let Some(d) = cheat {
        v = v + d;
    }
    let mut claim = v;
    let mut tr = init_transcript(p, &pd.tree0.root(), z, v);

    let mut sumcheck = Vec::with_capacity(p.s);
    let mut ts = Vec::with_capacity(p.s);
    let mut roots = Vec::new();
    let mut words: Vec<Vec<Fp2>> = Vec::new(); // w_1 .. w_{s-1}
    let mut trees: Vec<MerkleTree> = Vec::new();
    for j in 0..p.s {
        let mut h = [Fp2::ZERO; 3];
        for (ap, ep) in a.chunks_exact(2).zip(e.chunks_exact(2)) {
            h[0] = h[0] + ap[0] * ep[0];
            h[1] = h[1] + ap[1] * ep[1];
            h[2] = h[2] + (ap[1].double() - ap[0]) * (ep[1].double() - ep[0]);
        }
        if cheat.is_some() {
            // shift every value of h by half the discrepancy: h(0) + h(1) then equals the claim
            let d = (claim - (h[0] + h[1])) * Fp::new(2).inv();
            for x in h.iter_mut() {
                *x = *x + d;
            }
        }
        tr.absorb_field(b"sumcheck", &h);
        sumcheck.push(h);
        let t = tr.challenge_ext();
        claim = interp3(&h, t);
        ts.push(t);
        a = restrict(&a, t);
        e = restrict(&e, t);
        if j + 1 < p.s {
            let next = if j == 0 {
                fold_word(p.basis, &pd.w0, t, &inv_x0, 0, inv2)
            } else {
                fold_word(p.basis, &words[j - 1], t, &inv_x0, j, inv2)
            };
            let tree = MerkleTree::new(&next);
            tr.absorb_bytes(b"root", &tree.root());
            roots.push(tree.root());
            words.push(next);
            trees.push(tree);
        }
    }
    let mut g = a;
    if cheat.is_some() {
        // make the closure check pass by changing g(0)
        let prefix = ts.iter().zip(z).fold(Fp2::ONE, |acc, (&t, &zj)| acc * eq1(t, zj));
        let e0 = prefix * eq_table(&z[p.s..])[0];
        let cur = prefix * mle_eval(&g, &z[p.s..]);
        g[0] = g[0] + (claim - cur) * e0.inv();
    }
    tr.absorb_field(b"final", &g);

    let mut queries = Vec::with_capacity(p.queries);
    for _ in 0..p.queries {
        let i0 = tr.challenge_index(n);
        let l0 = i0 % (n / 2);
        let level0 = Opening { a: pd.w0[l0], b: pd.w0[l0 + n / 2], path: pd.tree0.path(l0) };
        let mut levels = Vec::new();
        for j in 1..p.s {
            let nj = n >> j;
            let l = i0 % (nj / 2);
            let w = &words[j - 1];
            levels.push(Opening { a: w[l], b: w[l + nj / 2], path: trees[j - 1].path(l) });
        }
        queries.push(QueryProof { level0, levels });
    }
    (v, Proof { sumcheck, roots, g, queries })
}

/// Verifier.
pub fn verify(p: &Params, root: &Digest, z: &[Fp2], v: Fp2, proof: &Proof) -> bool {
    verify_detail(p, root, z, v, proof).is_ok()
}

/// Verifier with the reason for rejection.
pub fn verify_detail(p: &Params, root: &Digest, z: &[Fp2], v: Fp2, proof: &Proof) -> Result<(), &'static str> {
    p.check();
    if z.len() != p.m
        || proof.sumcheck.len() != p.s
        || proof.roots.len() != p.s.saturating_sub(1)
        || proof.g.len() != 1 << (p.m - p.s)
        || proof.queries.len() != p.queries
    {
        return Err("shape");
    }
    let n = p.n();
    let omega = p.omega();
    let inv2 = Fp::new(2).inv();
    let mut tr = init_transcript(p, root, z, v);

    // sumcheck rounds
    let mut claim = v;
    let mut ts = Vec::with_capacity(p.s);
    for j in 0..p.s {
        let h = &proof.sumcheck[j];
        if h[0] + h[1] != claim {
            return Err("sumcheck");
        }
        tr.absorb_field(b"sumcheck", h);
        let t = tr.challenge_ext();
        claim = interp3(h, t);
        ts.push(t);
        if j + 1 < p.s {
            tr.absorb_bytes(b"root", &proof.roots[j]);
        }
    }
    tr.absorb_field(b"final", &proof.g);

    // closure
    let prefix = ts.iter().zip(z).fold(Fp2::ONE, |acc, (&t, &zj)| acc * eq1(t, zj));
    if claim != prefix * mle_eval(&proof.g, &z[p.s..]) {
        return Err("closure");
    }

    // G in monomial form
    let mut gc = proof.g.clone();
    to_coefficients(p.basis, &mut gc);

    // queries
    for q in &proof.queries {
        let i0 = tr.challenge_index(n);
        if q.levels.len() != p.s.saturating_sub(1) {
            return Err("query");
        }
        // level 0
        let l0 = i0 % (n / 2);
        if !verify_path(root, l0, &q.level0.a, &q.level0.b, &q.level0.path) {
            return Err("query");
        }
        if p.s == 0 {
            let x = omega.pow(i0 as u64);
            let val: Fp2 = if i0 < n / 2 { q.level0.a.into() } else { q.level0.b.into() };
            if val != horner(&gc, x.into()) {
                return Err("query");
            }
            continue;
        }
        let mut pair: (Fp2, Fp2) = (q.level0.a.into(), q.level0.b.into());
        let mut l = l0;
        for j in 0..p.s {
            let nj = n >> j;
            let x = omega.pow((l as u64) << j); // x = omega_j^l
            let inv_2x = (x.double()).inv();
            let folded = fold_pair(p.basis, pair.0, pair.1, inv_2x, ts[j], inv2);
            // folded is the value of w_{j+1} at index l of L_{j+1}
            if j + 1 < p.s {
                let o = &q.levels[j];
                let nn = nj / 2; // size of L_{j+1}
                let ln = l % (nn / 2);
                if !verify_path(&proof.roots[j], ln, &o.a, &o.b, &o.path) {
                    return Err("query");
                }
                let expected = if l < nn / 2 { o.a } else { o.b };
                if folded != expected {
                    return Err("query");
                }
                pair = (o.a, o.b);
                l = ln;
            } else {
                let y = omega.pow((l as u64) << (j + 1)); // omega_s^l
                if folded != horner(&gc, y.into()) {
                    return Err("query");
                }
            }
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn consistent_sumcheck_cheater_is_rejected() {
        // Commits Enc(f) honestly, claims v + 1, keeps every sumcheck check and the closure check
        // satisfied. Theorem 6.5 (case 2) predicts rejection; it happens in the query phase.
        let mut x = 99u64;
        let mut rnd = || {
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            Fp::new(x)
        };
        for (m, s) in [(6, 3), (8, 5), (8, 8), (10, 6)] {
            for basis in [Basis::Kernel, Basis::Monomial] {
            let p = Params { basis, m, log_inv_rate: 2, s, queries: 20 };
            let table: Vec<Fp> = (0..1 << m).map(|_| rnd()).collect();
            let z: Vec<Fp2> = (0..m).map(|_| Fp2(rnd(), rnd())).collect();
            let (root, pd) = commit(&p, &table);
            let (v, proof) = open_inner(&p, &pd, &z, Some(Fp2::ONE));
            assert_eq!(verify_detail(&p, &root, &z, v, &proof), Err("query"), "m={m} s={s}");
            // sanity: the honest proof for the same data is accepted
            let (v, proof) = open(&p, &pd, &z);
            assert!(verify(&p, &root, &z, v, &proof));
            }
        }
    }
}
