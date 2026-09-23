# Paper

*The Boolean-Kernel Basis: Native Evaluation-Form FRI Folding over Multiplicative Domains, with an Application to Multilinear Polynomial Commitments* — Abdelali Mkhida, September 2026.

- Compiled PDF: [`kbfold.pdf`](kbfold.pdf)
- Build: `latexmk -pdf main.tex` (or `make`)

| File | Content |
|---|---|
| `sections/01-introduction.tex` | §1 Introduction, contributions, related work |
| `sections/02-preliminaries.tex` | §2 Multilinear polynomials, smooth domains, Reed–Solomon codes, correlated agreement |
| `sections/02b-proof-systems.tex` | §3 IOPs, round-by-round soundness, sumcheck, PCS, BCS for IORs (CDHZ25) |
| `sections/03-kernel-basis.tex` | §4 The Boolean-kernel basis |
| `sections/04-fold-dictionary.tex` | §5 The fold dictionary |
| `sections/05-pcs.tex` | §6 The commitment scheme and completeness |
| `sections/06-soundness.tex` | §7 Soundness, binding, round-by-round knowledge, post-quantum security |
| `sections/07-implementation.tex` | §8 Implementation |
| `sections/08-experiments.tex` | §9 Experiments |
| `sections/09-conclusion.tex` | §10 Conclusion and open problems |
| `sections/10-notation.tex` | Appendix A: notation |
| `sections/11-lean.tex` | Appendix B: Lean formalisation |
