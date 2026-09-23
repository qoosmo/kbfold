# kbfold (Rust)

Reference implementation of the multilinear polynomial commitment scheme of the paper (§8–§9).

- `src/field.rs` — Goldilocks field $\mathbb{F}_p$, $p = 2^{64} - 2^{32} + 1$, and the quadratic extension $\mathbb{F}_p[\iota]/(\iota^2 - 7)$
- `src/poly.rs` — kernel ↔ monomial transforms, Möbius transform, restriction, multilinear evaluation, NTT
- `src/merkle.rs` — Merkle trees (one leaf per fibre) and the BLAKE3 Fiat–Shamir transcript
- `src/pcs.rs` — commit / open / verify, kernel encoding and the coefficient-form baseline

| Command | What it does |
|---|---|
| `cargo test --release` | completeness, tampering rejection, field facts ($p-1$ factorisation, 7 generates $\mathbb{F}_p^\times$) |
| `cargo run --release --example paper_checks` | 76 numerical checks of the paper's identities and lemmas (exhaustive over $\mathbb{F}_{17}$ where stated). Labels `sec4`/`sec5`/`sec6` refer to §5/§6/§7 of the final paper. The block marked "refuted early-draft conjecture" documents counterexamples to a claim that was removed and is not in the paper. |
| `cargo run --release --example pq_params` | exact rational evaluation of the post-quantum bound of Theorem 3.16 for the parameters of Remark 7.28 |
| `cargo run --release --example bench` | benchmarks of §9 (CSV outputs in `results/`) |

Research code: single-threaded, no SIMD, not audited, not constant-time. The post-quantum corollary of the paper applies to the compiler of CDHZ25 (salted Merkle trees), which this code does not yet implement.
