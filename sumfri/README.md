# Sum-FRI

**Hypercube Sums and Coefficient-Form Multilinear Evaluations from Shared-Challenge FRI Folding.**

A subproject of [KBFold](../README.md): the coefficient-form companion of the Boolean-kernel scheme, on the same Reed–Solomon code, with the same soundness machinery and Lean library.

| | What | Where |
|---|---|---|
| 📄 | Paper | [`paper/`](paper/) |
| ✅ | Lean 4 formalisation, built on the KBFold library (no `sorry`, one axiom) | [`../lean/SumFRI/`](../lean/SumFRI/), map: [`LEAN_MAP.md`](LEAN_MAP.md) |
| ⚙️ | Rust implementation and benchmarks, built on the `kbfold` crate | [`rust/`](rust/) |

**Paper:** `cd paper && latexmk -pdf main.tex`

**Lean:** `cd ../lean && lake build SumFRI && lake env lean SumFRI/Audit.lean`

**Rust:** `cd rust && cargo test --release`; benchmarks: `bench/run_all.sh <tag> 22 <whir_dir>`
