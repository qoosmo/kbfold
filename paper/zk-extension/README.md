# Kernel-Based Masking and Zero-Knowledge Folding

Public working manuscript developed chapter by chapter, reusing the kernel algebra and Lean formalization of the parent KBFold repository.

## Contents

- `main.tex`: standalone LaTeX entry point.
- `sections/01-introduction.tex`: Chapter 1, complete definitions and proofs.
- `references.bib`: primary historical and research references.
- `THEOREM_LEDGER.md`: statement-level dependencies and certification status.

## Build

```sh
pdflatex -interaction=nonstopmode -halt-on-error main.tex
biber main
pdflatex -interaction=nonstopmode -halt-on-error main.tex
pdflatex -interaction=nonstopmode -halt-on-error main.tex
```

## Scope

1. Binary-field ring switching and kernel coordinates.
2. Kernel-native masking and formal algebraic consistency.
3. Zero-knowledge extension of the original **odd-characteristic KBFold protocol** (masked sumcheck, folded oracles, closure, openings, simulator).
4. Complete proofs, Lean theorem map, and reproducible tests.

Existing KBFold algebraic results are reproved here where required for self-containedness. Each new claim is separated from the results established in prior work.

## Chapter order

1. Introduction and exact mathematical problem (complete)
2. Historical background and related work (complete)
3. Formal security model, online zero knowledge, and adaptive masking (complete)
4. Complete Boolean-kernel algebra (written, fully proved)
5. Multilinearization, normalized folding, linear masked closure, and joint query criteria (complete)
6. Characteristic-two kernel, Frobenius, trace and anchored consistency checker (complete)
7. Binary-field packing, trace, dual basis
8. Diamond--Posen ring switching
9. Kochergin masking
10. Kernel representation of transposition
11--16. Algebraic consistency, trace-zero masking, anchored kernels, protocol, soundness, simulation
17--20. Zero-knowledge KBFold over the original field
21--23. Costs, Lean mapping, reproducibility

Original reference: https://github.com/qoosmo/kbfold


## Chapter 2 results

- Historical mathematical progression: LFKN Sumcheck, Libra masking, FRI, BaseFold, Diamond--Posen, Kochergin, Frigo--shelat, and KBFold.
- Complete sumcheck completeness and soundness proofs.
- Zero-sum masking lemmas, including distributional conditions.
- Odd-characteristic word-fold/degree invariants.
- Exact high-degree mask propagation:
  pfold^j(X^N R) = X^(N/2^j) R_j, for N=2^m and 0 <= j <= m.
- Binary packing transposition and soundness of random multilinear batching.
- Trace/Frobenius correction, backward recurrence, and trace-zero characterization.
- A formal provenance and dependency ledger.


## Chapter 3 results

- Typed finite probability spaces, total variation, data processing, Markov hybrids.
- IOP oracle and adaptive verifier model; commitment correctness, binding, hiding definitions.
- Exact KBFold evaluation and proximity relations; Reed--Solomon distance and unique decoding.
- Round-by-round soundness and knowledge extraction.
- Statistical and online zero-knowledge games, including timing of commitment versus evaluation point.
- One-query leakage theorem for an unmasked codeword oracle.
- Adaptive linear-mask simulation via affine cosets and conditional distributions.
- Explicit counterexample proving that the high-degree polynomial mask requires a revised final-round closure.

See `CHAPTER_03_LEAN_MAP.md` for all 63 individually labeled definitions/results and their proposed Lean declarations.

**Scope:** Chapter 3 defines and proves the foundational security statements. It does not claim that the full zero-knowledge KBFold protocol has already been constructed or certified.

## Chapter 4 result

This chapter develops the original kernel basis over arbitrary fields, including the Kronecker transform, Möbius inverse, low-degree criterion, the exact evaluation curve, and the full tensor-functional formula for normalized folds. It separates odd characteristic from characteristic two. For a finite field, it proves that a uniformly chosen low-degree kernel mask gives secret-independent answers to at most `2^t` adaptive distinct nonzero queries to a **single** oracle of the form `P+X^N R`; the proof does not claim full ZK-KBFold. See `CHAPTER_04_LEAN_MAP.md`.

## Chapter 4 Rust regression tests

From `paper/zk-extension`, run `sh audit/RUN.sh`. This compiles a self-contained Rust test harness that checks kernel coordinate inversions, normalized fold identities, low-degree patterns, scaled evaluation curves, and an exhaustive two-query masking distribution. The CI workflow runs the Rust harness independently from the LaTeX build. These tests supplement but do not replace proofs.

The chapter also establishes an exact mask-budget versus code-rate tradeoff: for B=2^t, a degree-<B mask yields bounded-query hiding for B distinct nonzero oracle queries, while the Reed--Solomon degree bound becomes N+B.


## Chapter 5 results

The chapter contains **64 labeled definitions/results and 51 complete paper proofs** in seven subsections.

- All-prefix restrictions and multilinear evaluations.
- An explicit monomial/tensor functional for normalized folding over arbitrary fields, plus the characteristic-two specialization.
- Complete kernel-fold dictionary, including iterated/prefix composition.
- An injective and surjective masked encoding `(f,R) ↦ U_f+X^N R` for mask degree `< B ≤ N`.
- A precise level-wise mask propagation invariant `Q_j=U_(Res^j f)+X^(N/2^j)R_j`.
- **Revised linear final closure:** `Q_m(X)=MLE(f)(r)+rho_r(R)X` and `coeff_0(Q_m)=MLE(f)(r)`.
- Enlarged degree budgets `D_j=N/2^j+ceil(B/2^j)` and honest RS codeword-fold correctness.
- Local fold-check detection bounds, under explicit low-degree code membership.
- A necessary-and-sufficient image/coset criterion for jointly hiding fixed-schedule queries across folded oracles.
- A concrete one-query joint-leakage attack against a reused degree-zero mask, despite perfectly uniform individual messages.

**Security status:** All above are algebraic results. They do not prove the full ZK-KBFold protocol against malicious, adaptively querying verifiers. The masked sumcheck, authenticated online simulator, and adversarial proximity proof remain open.

See `CHAPTER_05_LEAN_MAP.md`. Run `sh audit/RUN.sh` for the original Chapter 4 and the new Chapter 5 Rust regression tests.


## Chapter 6 — Characteristic-Two Specializations

**Source:** `sections/06-binary.tex` and eight proof-oriented subsections.
**Lean map:** [CHAPTER_06_LEAN_MAP.md](CHAPTER_06_LEAN_MAP.md).
**Audit:** 85 separately labeled statements, including **67 full paper proofs** and 18 typed definitions. The new Chapter 6 results are **not yet Lean-certified**.

### Proven algebraic results

- Characteristic-two Frobenius on scalars and polynomial coefficients, including field and kernel covariance.
- The partition identity `sum_b K_b(X)=1`, and complete/partial multilinearization by explicit monomial expansion.
- Absolute trace and Artin--Schreier: `im(t²+t)=ker(Tr)`, uniform trace-zero masking.
- Existence of a full-degree field element, a kernel evaluation basis and its trace-dual coordinate basis.
- Exact affine kernel-correction identity `Tr(V_k)=coord_k(D_c+Delta_p)`.
- Uniformity of independently masked public trace-zero messages for a fixed consistent instance.
- Unanchored residual collision and construction of the minimal-degree anchored family `{1,W_b}`.
- Root bound `n/2^n` for a fixed nonzero anchored residual.
- Perfect algebraic completeness and two-challenge **coefficient-consistency** bound `(ell+n)/2^n` for fixed `p,c` before `theta`, with all residuals fixed before `z`.
- Proof that a binary field has no even-order multiplicative subgroup, so KBFold's original odd-characteristic `±x` word fold does not directly carry over.

### Security boundary

The chapter proves *an algebraic consistency checker*, **not** zero knowledge for the entire Ring Switching protocol or the odd-characteristic KBFold PCS. In particular it does not establish the joint distribution of the public vector `U` together with the later scalar `A`, a hiding authenticated commitment, or a full online simulator.

### Reproducible audit

Run `sh audit/RUN.sh` to execute the existing kernel tests plus the new deterministic GF(16) and GF(256) tests covering basis, trace duality, affine equations, honest checks and anchored root counts. These tests supplement the full mathematical proofs.
