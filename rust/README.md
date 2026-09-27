# kbfold

Reference implementation of **KBFold**, a hash-based multilinear polynomial commitment scheme
built on the Boolean-kernel basis: the table of a multilinear polynomial is encoded in the basis
of kernel polynomials, and FRI folding acts natively on evaluation form over multiplicative domains.

- Paper: [The Boolean-Kernel Basis (PDF)](https://github.com/qoosmo/kbfold/blob/main/paper/kbfold.pdf).
- The mathematics of the paper is machine-checked in Lean 4
  ([`lean/`](https://github.com/qoosmo/kbfold/tree/main/lean)).

## Usage

```rust
use kbfold::field::{Fp, Fp2};
use kbfold::pcs::{Basis, Params, commit, open, verify};

// m = 16 variables, rate 1/4, 12 folding rounds, 148 queries
let p = Params { basis: Basis::Kernel, m: 16, log_inv_rate: 2, s: 12, queries: 148 };
let table: Vec<Fp> = (0..1u64 << 16).map(Fp::new).collect(); // f on {0,1}^16
let z: Vec<Fp2> = (0..16u64).map(|i| Fp2(Fp::new(3 + i), Fp::new(7 * i))).collect();

let (root, pd) = commit(&p, &table);
let (v, proof) = open(&p, &pd, &z); // v = f(z)
assert!(verify(&p, &root, &z, v, &proof));
```

## Modules

| Module | Contents |
|---|---|
| `field` | Goldilocks F_p, p = 2^64 - 2^32 + 1, and the quadratic extension F_p[u]/(u^2 - 7) |
| `poly` | kernel and monomial transforms, Moebius transform, restriction, multilinear evaluation, NTT |
| `merkle` | Merkle trees (one leaf per fibre, BLAKE3 in keyed mode) and the Fiat-Shamir transcript |
| `pcs` | `Params`, `commit`, `open`, `verify`, `verify_detail`; kernel form (`Basis::Kernel`) and the coefficient-form baseline (`Basis::Monomial`) |

## Commands

```bash
cargo test --release                          # completeness, tampering rejection, field facts
cargo run --release --example paper_checks    # 76 numerical checks of the paper's identities and lemmas
cargo run --release --example pq_params       # exact post-quantum bound of the paper
cargo run --release --example bench           # benchmarks of the paper
```

## Status

Research code: single-threaded, no SIMD, not audited, not constant-time. The post-quantum
corollary of the paper applies to the compiler of Chiesa-Di-Hu-Zheng (salted Merkle trees); this
code uses unsalted trees, so the corollary is not claimed for it. Zero knowledge is not provided.

## License

MIT or Apache-2.0, at your option.
