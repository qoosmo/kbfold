//! kbfold: post-quantum multilinear polynomial commitments from FRI folding in the Boolean-kernel
//! basis.
//!
//! Reference implementation of "Post-Quantum Multilinear Polynomial Commitments from FRI Folding
//! in the Boolean-Kernel Basis",
//! <https://github.com/qoosmo/kbfold/blob/main/paper/kbfold.pdf>.
//!
//! ```
//! use kbfold::field::{Fp, Fp4};
//! use kbfold::pcs::{Params, commit, open, verify};
//!
//! // m = 10 variables, rate 1/4, 6 folding rounds, 248 queries, challenges in F_{p^4}
//! let p = Params::post_quantum(10);
//! let table: Vec<Fp> = (0..1u64 << 10).map(Fp::new).collect(); // f on {0,1}^10
//! let z: Vec<Fp4> = (0..10u64).map(|i| Fp4::from(Fp::new(3 + i))).collect();
//! let (root, pd) = commit(&p, &table)?;
//! let (v, proof) = open(&p, &pd, &z)?; // v = f~(z)
//! verify(&p, &root, &z, v, &proof)?;
//! # Ok::<(), kbfold::error::Error>(())
//! ```
//!
//! Modules: `field` (Goldilocks and its quadratic and quartic extensions), `poly` (kernel and
//! monomial transforms, Moebius transform, restriction, NTT), `merkle` (salted Merkle trees and
//! the Fiat-Shamir transcript), `pcs` (commit, open, verify, in kernel form and in the
//! coefficient-form baseline), `error`.
//!
//! The prover draws its salts from the operating system (`getrandom`). The verifier returns
//! `Result` and never panics on a malformed proof. Research code, single-threaded, not audited.

#![forbid(unsafe_code)]

pub mod error;
pub mod field;
pub mod merkle;
pub mod pcs;
pub mod poly;
mod rand;

/// Seeded provers for test vectors and reproducible digests (feature `insecure-test-vectors`).
///
/// **Insecure:** the seed determines every salt of the proof, so a reused or public seed makes
/// the salts predictable. Never enable this feature in production code.
#[cfg(feature = "insecure-test-vectors")]
#[doc(hidden)]
pub mod insecure {
    use crate::error::Error;
    use crate::field::{ExtField, Fp};
    use crate::merkle::Digest;
    use crate::pcs::{Params, Proof, ProverData};

    pub fn commit(p: &Params, table: &[Fp], seed: &Digest) -> Result<(Digest, ProverData), Error> {
        crate::pcs::commit_seeded(p, table, seed)
    }
    pub fn open<E: ExtField>(
        p: &Params,
        pd: &ProverData,
        z: &[E],
        seed: &Digest,
    ) -> Result<(E, Proof<E>), Error> {
        crate::pcs::open_seeded(p, pd, z, seed)
    }
}
