# Sum-FRI

**Hypercube Sums and Coefficient-Form Multilinear Evaluations from Shared-Challenge FRI Folding.**

A subproject of [KBFold](../README.md): the coefficient-form companion of the Boolean-kernel scheme, on the same Reed–Solomon code, with the same soundness machinery and Lean library.

| | What | Where |
|---|---|---|
| 📄 | Paper | [`paper/`](paper/) |
| ✅ | Lean 4 formalisation, built on the KBFold library | [`../lean/SumFRI/`](../lean/SumFRI/) (library `SumFRI` of the KBFold Lean project) |
| ⚙️ | Rust implementation and benchmarks, built on the `kbfold` crate | [`rust/`](rust/) |

**Paper:** `cd paper && latexmk -pdf main.tex`
