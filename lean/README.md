# KBFold — Lean 4 formalisation

Machine-checked proofs of the mathematics of the paper (§2–§7).

- Lean `4.23.0`, Mathlib `v4.23.0` (pinned in `lake-manifest.json`).
- 16 modules, about 7,000 lines. **No `sorry`.**
- **One axiom:** `bciks_unique` in `KBFold/BCIKS.lean`, the correlated-agreement theorem of Ben-Sasson, Carmon, Ishai, Kopparty and Saraf (Theorem 2.23 of the paper).

```bash
lake exe cache get      # prebuilt Mathlib
lake build              # builds all modules
lake env lean KBFold/Audit.lean   # #print axioms for the main theorems
```

| Module | Paper |
|---|---|
| `Multilinear` | §2.3 equality polynomial, multilinear extension, restriction, naturality |
| `Kernel` | §4 kernel polynomials, basis theorem; §5 even/odd split, `fold_dictionary` |
| `Domain` | §2 smooth domains, power maps, fibres, Reed–Solomon codes, unique decoding |
| `WordFold` | §5 word folds, line form, fold consistency, classical FRI fold |
| `LowDegree`, `Mobius` | §4 Kronecker structure, coefficient formulas, low-degree criterion, evaluation identity; §2 Möbius |
| `Probability` | §3 finite probability, sequential challenges, independent queries, randomised provers |
| `RoundByRound` | §3 soundness notions, round-by-round ⇒ overall, sumcheck, knowledge ⇒ binding |
| `BCIKS` | the axiom (Theorem 2.23) |
| `Fibre` | §7.1–7.3 fibre distance, decoding, folding lemmas, good challenges |
| `Protocol`, `Completeness` | §6 the evaluation protocol, honest prover, completeness |
| `Soundness` | §7.4–7.5 passing sets, codeword chain, soundness theorem, binding, ℓ = 0 |
| `RBR`, `RBRGeneric` | §7.6 doomed sets, round-by-round knowledge soundness |
| `NonInteractive` | §7.7 fibre strings, sampling, erasures, relaxed round-by-round knowledge, witness uniqueness |

Full correspondence: [`../docs/LEAN_MAP.md`](../docs/LEAN_MAP.md).

**Modelling notes.** Bit vectors are `Fin n → Bool`; Lean bit `k` is paper bit `k+1`. A single field `F` is used, and the domain is a subgroup `L ≤ Fˣ`. Probabilities are rationals, computed by counting over finite uniform spaces. Provers are deterministic, with explicit causality hypotheses. Decoding is non-constructive, and running times are not formalised.
