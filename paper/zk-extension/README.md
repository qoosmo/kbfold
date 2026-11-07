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
7. Binary-field packing, inverse transposition and complete Ring Switching equations (complete)
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


## Chapter 7 — Binary-Field Packing and Transposition

**Source:** `sections/07-packing.tex` with seven proof-oriented subsections.
**Lean map:** [CHAPTER_07_LEAN_MAP.md](CHAPTER_07_LEAN_MAP.md).
**Audit:** 71 labeled definitions/results: 22 definitions and **49 complete paper proofs**. None of these Chapter 7 declarations has yet been machine checked in Lean 4.

### Established mathematical results

- Lossless $\F_2$-basis packing, inverse extraction, bit-column identities, and original two-axis multilinear evaluation.
- Exact coordinate-matrix transpose, involution $\mathcal T^2=\mathrm{id}$, proof of $\F_2$-linearity, and proof that it is not $L$-linear for $n>1$.
- Packed transposition identity $\mathcal T(s^*)_u=\sum_jd_u(h_j)\widehat w_j$, random batching $B_{s^*}=\sum_j a_j\widehat w_j$, and a degree-$\ell$ discrepancy test.
- Independent uniform pads $p,p_{\mathrm{in}}$, uniform public $(m,y')$, pad correction $C_p$, and complete IN/OUT/CLAIM affine equations.
- Error decomposition $\mathsf{OUT\ residual}=B_{m+s^*+p}+D_{c+c^p}$, exact honest completeness and conditional algebraic soundness at most $(\ell+n)/2^n$ against false evaluation claims.
- Trace-dual field-affine implementation interface and an explicit proof that exposing $(m,c^p)$ recovers $s^*$.
- An ideal-to-implementation soundness union bound, conditional on independently proving external commitment/affine-proof failures.

**Open:** External PCS soundness, binding to packed bits, authenticated openings, joint online simulator for $m,y',U,A$, and application to the odd-characteristic KBFold IOP.

**Reproducibility:** Chapter 7 Rust tests exercise packed Ring Switching identities and masking over GF(16) and GF(256).


## Chapter 8 — Original Diamond--Posen Tensor Ring-Switching Compiler

**Source:** `sections/08-diamond-posen.tex` and seven detailed subsections.
**Lean map:** [CHAPTER_08_LEAN_MAP.md](CHAPTER_08_LEAN_MAP.md).
**Paper audit:** 56 labeled definitions/results and **41 complete proofs**. None of the new Chapter 8 declarations has yet been Lean-certified.

### Mathematical results proved in this chapter

- Tensor algebra $A=L\otimes_{\F_2}L$, commuting embeddings $\varphi_0,\varphi_1$, explicit left-$L$ column coordinates and contraction.
- Identity $\operatorname{Col}(\varphi_1(T')(\varphi_0(r_{\rm hi})))_v=s_v^*$ and $y_w=C_q(S)$, without replacing the tensor by ordinary field multiplication.
- Degree-two tensor-valued sumcheck summand $H$ and exact Boolean-sum relation $\sum_b H(b)=S$.
- Ring root-count lemma: a nonzero polynomial of degree at most $d$ has at most $d$ roots among values $\varphi_1(z)$, $z\in L$, because their pairwise differences are units in $A$.
- Causal degree-two sumcheck with algebraic soundness at most $2h/|L|$.
- Faithful Construction 4.1 reduction to a bound committed large-field multilinear polynomial, perfect completeness, and conditional false-claim soundness at most $2h/|L|+\varepsilon_{\mathrm{eval}}$.
- Explicit privacy obstruction: the unmasked $A$-valued initial message reveals every partial evaluation; two equal-evaluation witnesses can be perfectly distinguished by one tensor column.
- Strict separation from the masked kernel-coordinate checker of Chapters 6--7 and its still-unproved online zero-knowledge simulator.

**Important attribution:** Diamond and Posen (ePrint 2024/504, §4) introduced this original tensor-algebra compiler; its reconstruction is not claimed as our novel result. The later mask techniques of Kochergin and Frigo--shelat are cited independently.

**Rust audit:** GF(16)/GF(256) tests for tensor multiplication, embeddings, exact columns, original evaluation, terminal factor and the embedded-field polynomial root bound.


## Chapter 9 — Zero-Knowledge Ring Switching

**Source:** `sections/09-zk-ring-switching.tex`, seven subsections.
**Lean map:** [CHAPTER_09_LEAN_MAP.md](CHAPTER_09_LEAN_MAP.md).
**Proof audit:** 51 labeled definitions/results and **37 complete mathematical proofs**. The newly proposed Lean 4 declarations have not been certified.

### Proved facts

- Exact causal one-opening public-core simulation: the joint view `(m,y',theta,U,z,A)` is independent of an admissible witness, even under adaptively chosen verifier challenges, provided fresh independent field masks are used.
- Uniform input pair `(m,y')`, uniform conditional trace-zero vector `U`, and uniform conditional final field scalar `A`.
- Exact conditional Artin--Schreier mask fibers (two preimages per coordinate), and existence/count of hidden witness completions.
- Every enforced hidden-field consistency relation is affine after public challenges; the public check uses `Tr(U_k)=0`. Hidden quadratic `sigma=rho²` is tested probabilistically through anchored residuals rather than directly proved.
- Nonzero residual root error at most `n/|L|`; ideal false-claim soundness at most `(ell+n)/|L|` with all commitment/challenge timing explicit.
- A two-opening pad-reuse attack distinguishing equal-authorized-evaluation witnesses with statistical distance one.
- Perfect complete-view privacy in a deliberately **opaque ideal proof functionality**, plus a conditional real-world ZK composition theorem assuming a separate full commitment/proof/authenticated-opening simulator.
- Exact single-opening message and auxiliary-state counts and the characteristic-two versus existing odd-characteristic KBFold obstacle.

**Security boundary:** Chapter 9 does **not** establish unconditional real-world zero knowledge for the complete KBFold PCS. Concrete binding, hiding, online simulation of all commitment roots/proofs/openings, and the original KBFold degree/proximity arguments remain to be proved.

**Reproducible tests:** Chapter 9 has deterministic finite-field regression tests of public message distributions and conditional mask laws over GF(4) and GF(16).
