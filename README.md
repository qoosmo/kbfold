# KBFold

**The Boolean-Kernel Basis: native evaluation-form FRI folding over multiplicative domains, with an application to multilinear polynomial commitments.**

[![Lean](https://github.com/qoosmo/kbfold/actions/workflows/lean.yml/badge.svg)](https://github.com/qoosmo/kbfold/actions/workflows/lean.yml)
[![Rust](https://github.com/qoosmo/kbfold/actions/workflows/rust.yml/badge.svg)](https://github.com/qoosmo/kbfold/actions/workflows/rust.yml)
[![Paper](https://github.com/qoosmo/kbfold/actions/workflows/paper.yml/badge.svg)](https://github.com/qoosmo/kbfold/actions/workflows/paper.yml)
![Lean 4.23.0](https://img.shields.io/badge/Lean-4.23.0-blue)
![Mathlib v4.23.0](https://img.shields.io/badge/Mathlib-v4.23.0-blue)
![sorry-free](https://img.shields.io/badge/sorry-0-brightgreen)

This repository contains three things that describe one object:

| | What | Where |
|---|---|---|
| 📄 | A self-contained paper (55 pages): definitions, theorems and full proofs | [`paper/`](paper/) · [PDF](paper/kbfold.pdf) |
| ✅ | A Lean 4 formalisation of the paper's mathematics (16 modules, ~7,000 lines, no `sorry`) | [`lean/`](lean/) |
| ⚙️ | A Rust reference implementation of the commitment scheme, with benchmarks | [`rust/`](rust/) |

## The idea in one paragraph

BaseFold-style polynomial commitments fold a Reed–Solomon codeword while running a sumcheck. Over smooth multiplicative domains, the classical FRI fold acts on **monomial coefficients**, so a prover holding a multilinear polynomial as a **table of values** must first change representation. We introduce the Boolean-kernel basis

$$K_b(X) = \prod_{k=1}^{n} \bigl(X^{2^{k-1}} + b_k\bigr), \qquad b \in \{0,1\}^n,$$

of the polynomials of degree $< 2^n$. In this basis a normalised FRI fold is **exactly** the restriction of one variable of the multilinear extension of the coordinate table (the *fold dictionary*). Folding the codeword of $\sum_b f(b) K_b$ therefore evaluates $\tilde f$ directly: the committed word, the sumcheck table and the folds are three views of one object.

## Main results

- **Basis theorem.** $\{K_b\}$ is a basis of $\mathbb{F}[X]_{<2^n}$; the change of basis to monomials is a Kronecker power of a $2\times2$ matrix and costs $\tfrac{n}{2}2^n$ additions.
- **Fold dictionary.** $\mathrm{pfold}_r\bigl(\sum_b \lambda(b) K_b\bigr) = \sum_{b'} \mathrm{res}_r(\lambda)(b')\, K_{b'}$.
- **Low degree and evaluation.** A sign-condition characterisation of low degree in kernel coordinates; univariate evaluation as a scaled multilinear evaluation.
- **Commitment scheme.** A transparent, hash-based multilinear PCS (BaseFold paradigm, kernel encoding), with proofs of:
  - completeness;
  - soundness and evaluation binding in the unique-decoding regime;
  - round-by-round knowledge soundness with an explicit decoding extractor.

  The only external ingredient about codes is the correlated-agreement theorem of BCIKS.
- **Post-quantum security.** From round-by-round knowledge soundness we derive the *relaxed* round-by-round knowledge soundness of Chiesa–Di–Hu–Zheng (ePrint 2025/2166).
  - By their BCS theorem for interactive oracle reductions, the non-interactive scheme is knowledge sound against **quantum** adversaries in the QROM, with explicit concrete bounds.
  - This holds even though the adversary chooses the Merkle-committed commitment.
  - Example parameters: $2^{64}$ queries, error $< 2^{-31.8}$, with κ = 248 queries and a 256-bit hash.

## Verification status

| Part | Paper | Lean | Other checks |
|---|---|---|---|
| Multilinear toolkit, smooth domains, RS codes (§2) | proved | ✅ formalised | — |
| IOPs, round-by-round soundness, sumcheck (§3.1–3.4) | proved | ✅ formalised | — |
| Kernel basis, low degree, evaluation (§4) | proved | ✅ formalised | `paper_checks`, $n \le 6$ |
| Fold dictionary, word folds, classical fold (§5) | proved | ✅ formalised | `paper_checks`, $n \le 6$ |
| Completeness (§6) | proved | ✅ formalised | Rust tests, `paper_checks` |
| Soundness, binding, RBR knowledge (§7.1–7.6) | proved | ✅ formalised, axiom BCIKS | exhaustive checks over $\mathbb{F}_{17}$ in `paper_checks` |
| Relaxed RBR knowledge, erasures (§7.7) | proved | ✅ formalised, axiom BCIKS | two independent reviews |
| Post-quantum corollary (Thm 3.16, Cor 7.26) | theorem quoted from CDHZ25, specialisation proved | — (quantum model) | exact parameter computation (`pq_params`) |
| Correlated agreement (BCIKS Thm 4.1) | quoted | the single axiom `bciks_unique` | — |

Details: [`docs/VERIFICATION.md`](docs/VERIFICATION.md) · paper ↔ Lean map: [`docs/LEAN_MAP.md`](docs/LEAN_MAP.md).

## Repository layout

```
paper/     LaTeX sources, bibliography, compiled PDF
lean/      Lake project KBFold (Lean 4.23.0 + Mathlib v4.23.0)
rust/      kbfold crate: field (Goldilocks + quadratic extension), NTT, Merkle, PCS; tests, benchmarks, checks
checks/    Python reference for the post-quantum parameter computation
docs/      verification report, paper↔Lean map, roadmap
```

## Quick start

**Lean** (checks every formalised theorem; downloads the Mathlib cache):
```bash
cd lean
lake exe cache get
lake build
lake env lean KBFold/Audit.lean    # prints the axioms used by the main theorems
```

**Rust** (Rust ≥ 1.85):
```bash
cd rust
cargo test --release                          # completeness, tampering, field facts
cargo run --release --example paper_checks    # numerical checks of the paper's lemmas
cargo run --release --example pq_params       # exact post-quantum bound (Remark 7.28)
cargo run --release --example bench           # benchmarks of Section 9
```

**Paper**:
```bash
cd paper && latexmk -pdf main.tex
```

## Scope and limitations

- **Unique decoding only.** The soundness analysis stays in the unique-decoding regime. List-decoding analyses need fewer queries; extending to them is future work.
- **One opening per proof.** The analysis covers one commitment opened at one point per proof; batching and multiple openings are not analysed.
- **The code is not covered by the post-quantum corollary yet.** The corollary applies to the compiler of CDHZ25 (Construction 11.7: salted Merkle trees and their challenge derivation). The Rust code uses unsalted, domain-separated Merkle trees, a BLAKE3 transcript and a quadratic extension. Aligning the two is on the [roadmap](docs/ROADMAP.md).
- **No speed claim.** The scheme is not claimed faster than BaseFold or DeepFold. The contribution is the basis and the dictionary.
- **Not production code.** The implementation is single-threaded research code and has not been audited.

## Citation

```bibtex
@misc{Mkhida2026KBFold,
  author = {Abdelali Mkhida},
  title  = {The Boolean-Kernel Basis: Native Evaluation-Form {FRI} Folding over Multiplicative Domains,
            with an Application to Multilinear Polynomial Commitments},
  year   = {2026},
  note   = {Paper, Lean 4 formalisation and Rust implementation},
  howpublished = {\url{https://github.com/qoosmo/kbfold}}
}
```
See also [`CITATION.cff`](CITATION.cff).

## Author

**Abdelali Mkhida** — independent researcher, Algorizk Labs · ORCID [0009-0009-2101-9070](https://orcid.org/0009-0009-2101-9070) · ali.mkhida@algorizk.xyz

## License

To be decided. Until a license file is added, all rights are reserved.
