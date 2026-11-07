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
3. Security model and preliminaries
4. Full Boolean-kernel algebra
5. Multilinearization and fold identities
6. Characteristic-two specializations
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
