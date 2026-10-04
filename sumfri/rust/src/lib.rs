//! sumfri: hypercube sums and coefficient-form multilinear evaluations from shared-challenge FRI
//! folding.
//!
//! Reference implementation of the Sum-FRI paper (`sumfri/paper` in the KBFold repository). It
//! is built on the [`kbfold`] crate, from which it takes the field (Goldilocks and its quadratic
//! and quartic extensions), the NTT, the salted Merkle trees and the Fiat-Shamir transcript.
//!
//! ```
//! use kbfold::field::{Field, Fp, Fp2};
//! use sumfri::pcs::{Params, commit, open_sum, verify_sum};
//!
//! let p = Params::classical(10); // m = 10, rate 1/4, 6 folding rounds, 148 queries
//! let table: Vec<Fp> = (0..1u64 << 10).map(Fp::new).collect();
//! let (root, pd) = commit(&p, &table)?;
//! let (v, proof) = open_sum::<Fp2>(&p, &pd)?; // v = sum_a f(a)
//! assert_eq!(v, Fp2::from(table.iter().fold(Fp::ZERO, |s, &x| s + x)));
//! verify_sum(&p, &root, v, &proof)?;
//! # Ok::<(), kbfold::error::Error>(())
//! ```
//!
//! Modules: `pcs` (commit, open, verify for `Pi_eval` and `Pi_sum`), `quotient` (the baseline
//! that opens `V_f` at `X = 1` with a quotient and a FRI low-degree test). The verifiers return
//! `Result` and never panic on a malformed proof. Research code, not audited.

#![forbid(unsafe_code)]

mod par;
pub mod pcs;
pub mod quotient;
mod rand;

/// Seeded provers for reproducible tests (feature `insecure-test-vectors`). Insecure.
#[cfg(feature = "insecure-test-vectors")]
#[doc(hidden)]
pub mod insecure {
    use kbfold::error::Error;
    use kbfold::field::{ExtField, Fp};
    use kbfold::merkle::Digest;
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
