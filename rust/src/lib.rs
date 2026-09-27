//! kbfold: a multilinear polynomial commitment scheme from the Boolean-kernel basis.
//!
//! Reference implementation of "The Boolean-Kernel Basis: Native Evaluation-Form FRI Folding
//! over Multiplicative Domains, with an Application to Multilinear Polynomial Commitments",
//! <https://github.com/qoosmo/kbfold/blob/main/paper/kbfold.pdf>.
//!
//! ```
//! use kbfold::field::{Fp, Fp2};
//! use kbfold::pcs::{Basis, Params, commit, open, verify};
//!
//! // m = 10 variables, rate 1/4, 6 folding rounds, 148 queries
//! let p = Params { basis: Basis::Kernel, m: 10, log_inv_rate: 2, s: 6, queries: 148 };
//! let table: Vec<Fp> = (0..1u64 << 10).map(Fp::new).collect(); // f on {0,1}^10
//! let z: Vec<Fp2> = (0..10u64).map(|i| Fp2(Fp::new(3 + i), Fp::new(7 * i))).collect();
//! let (root, pd) = commit(&p, &table);
//! let (v, proof) = open(&p, &pd, &z); // v = f(z)
//! assert!(verify(&p, &root, &z, v, &proof));
//! ```
//!
//! Modules: `field` (Goldilocks and its quadratic extension), `poly` (kernel and monomial
//! transforms, Moebius transform, restriction, NTT), `merkle` (Merkle trees and the Fiat-Shamir
//! transcript), `pcs` (commit, open, verify, in kernel form and in the coefficient-form baseline).
//! Research code: single-threaded, not audited, unsalted Merkle trees.

pub mod field;
pub mod merkle;
pub mod pcs;
pub mod poly;
