# Task: prove `KBFold.bciks_unique` (remove the project's only axiom)

You are working in the Lean 4 project in this directory (`lean/` of the KBFold repository,
branch `sumfri`). Toolchain `leanprover/lean4:v4.23.0`, Mathlib pinned at `v4.23.0`
(`lakefile.lean`). Two libraries: `KBFold` and `SumFRI`. Both compile today with exactly one
project axiom, `KBFold.bciks_unique`, in `KBFold/BCIKS.lean`.

**Goal.** Replace `axiom bciks_unique` by `theorem bciks_unique` with **exactly the same name,
binders and statement**, proved without `sorry` and without any new axiom. Nothing else in the
project may change its statement.

## The statement (do not modify)

```lean
axiom bciks_unique {F : Type*} [Field F] [Fintype F] (L : Subgroup Fˣ) (μ : ℕ)
    (hL : IsSmoothDomain L μ) (d : ℕ) (hd : 1 ≤ d) (hdM : d ≤ Nat.card L)
    (δ : ℚ) (hδ0 : 0 < δ) (hδ : δ ≤ (1 - rate L d) / 2) (u0 u1 : L → F)
    (hS : Nat.card L < {r : F | DistLE (u0 + r • u1) (RS L d : Set (L → F)) δ}.ncard) :
    ∃ L' : Set L, (1 - δ) * Nat.card L ≤ L'.ncard ∧
      ∃ c0 ∈ RS L d, ∃ c1 ∈ RS L d, ∀ ξ ∈ L', u0 ξ = c0 ξ ∧ u1 ξ = c1 ξ
```

Definitions used (all in `KBFold/Domain.lean`):
- `IsSmoothDomain L μ : Nat.card L = 2 ^ μ` (smoothness is **not** needed by the proof; only
  that `L` is a finite set of distinct field elements, `n := Nat.card L ≥ 1`).
- `ev L P : L → F := fun ξ => P.eval ξ`; `RS L d := (degreeLT F d).map (evLin L)`;
  `mem_RS : c ∈ RS L d ↔ ∃ P ∈ degreeLT F d, ev L P = c`.
- `rate L d := d / Nat.card L`.
- `hdist w w' := {i | w i ≠ w' i}.ncard`, `relDist w w' := hdist w w' / Nat.card ι`,
  `DistLE w C δ := ∃ c ∈ C, relDist w c ≤ δ`, `agreeSet`, `agree_add_hdist`.

Source: Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity gaps for Reed–Solomon codes*,
J. ACM 2023 (ePrint 2020/654), **Theorem 4.1** and its proof in §4 (unique decoding, via
Berlekamp–Welch over `F[Z]`). Read that proof first.

## Mathematical proof plan

Notation: `n = |L|`, `e = ⌊δ n⌋`, `w_z = u0 + z u1` for `z ∈ F`, `S = {z : Δ(w_z, RS) ≤ δ}`,
`|S| > n`.

0. **Arithmetic.** From `δ ≤ (1 − d/n)/2`: `2e ≤ n − d`, hence `d + 2e ≤ n` and `e + 1 ≤ n`.
   For `z ∈ S`: `hdist(w_z, c) ≤ δn` with an integer left side, so `hdist(w_z, c) ≤ e`.
1. **Unique decoding lemma (over `F`).** If `P ∈ F[X]_{<d}` with `hdist(w, ev P) ≤ e`, and
   `E` monic of degree `e`, `Q ∈ F[X]_{<e+d}` with `Q(x) = E(x) w(x)` for all `x ∈ L`, then
   `Q = E P`. (`Q − E P` has degree `< e + d` and vanishes on the `≥ n − e ≥ d + e` agreement
   points.) Corollary: the decoded `P_z` is unique for `z ∈ S`.
2. **Local solutions.** For `z ∈ S` there are `E_z` monic of degree `e` and `Q_z` of degree
   `< e + d` with `Q_z = E_z w_z` on `L` (error locator padded by a power of `X`, and
   `Q_z = E_z P_z`).
3. **Lift to `F[Z]` (the key step, BCIKS §4).** The Berlekamp–Welch system in the unknown
   coefficients of `E` (monic, degree `e`) and `Q` (degree `< e + d`) has coefficients affine in
   `Z`; only the `e` columns of `E` and the right-hand side involve `Z`. It is solvable at every
   `z ∈ S`, and `|S| > n ≥ e + 1`, so it is solvable over `F(Z)` (a nonzero minor of the
   augmented matrix would be a polynomial of `Z`-degree `≤ e + 1` vanishing on `S`). Clear
   denominators (Cramer) to get `E(X,Z), Q(X,Z)` with polynomial coefficients and bounded
   `Z`-degree, and use step 1 at the points of `S` where the denominator does not vanish, plus
   degree counting in `Z`, to conclude `Q = E · P` with `P(X,Z) = P0(X) + Z P1(X)`,
   `P0, P1 ∈ F[X]_{<d}`. Follow BCIKS for the exact degree bookkeeping; `|S| > n` is what it
   needs.
4. **Agreement set.** `E(X, Z)` has `X`-degree `e`, so (choosing it appropriately, as in BCIKS)
   the set `B ⊆ L` of points where `u0 ≠ ev P0` or `u1 ≠ ev P1` has at most `e ≤ δn` elements.
   Take `L' = L \ B`, `c0 = ev P0`, `c1 = ev P1`; then `|L'| ≥ n − e ≥ (1 − δ) n`.

You may choose a different correct route (e.g. a different but complete algebraic argument), as
long as the final theorem statement is unchanged.

## Lean guidance

- Put the proof in **new modules** (e.g. `KBFold/BCIKSProof/*.lean`) importing
  `KBFold.Domain` and Mathlib; then make `KBFold/BCIKS.lean` import them and turn the axiom
  into `theorem bciks_unique ... := ...`. Do not create import cycles (`BCIKS.lean` is imported
  by `KBFold.Fibre`).
- Likely useful Mathlib (check exact names with `#check` / lean-lsp search before use):
  `Polynomial.degreeLT`, `Polynomial.mem_degreeLT`, `Polynomial.divByMonic`, `modByMonic`,
  `Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero` (or `card_roots'`),
  `Polynomial.Monic`, `RatFunc`, `Matrix.rank`, `Matrix.det`, `Matrix.updateCol`
  (Cramer: `Matrix.cramer`), `Lagrange.interpolate`, `Set.ncard` / `Finset.card` lemmas.
- Do **not** upgrade Mathlib or the toolchain.
- `set_option autoImplicit false` is the project default.

## Rules

1. After every new lemma: `lake build KBFold` (and at the end `lake build SumFRI`). Never commit
   a non-building state.
2. Commit after each completed step with a clear message.
3. No `sorry`, no `admit`, no new `axiom`, no `set_option maxHeartbeats 0` (bounded increases
   with a comment are acceptable).
4. Do not change any existing statement except `axiom` → `theorem` for `bciks_unique`.
5. Keep docstrings in the project's style; cite BCIKS23 Theorem 4.1 and the KBFold paper's
   Theorem 2.23.
6. If you get stuck, write what is done, what remains and the exact blocking goal in the
   **Status** section below, commit, and stop.

## Acceptance check

```bash
cd lean
lake build KBFold SumFRI
lake env lean KBFold/Audit.lean    # no theorem may list KBFold.bciks_unique
lake env lean SumFRI/Audit.lean
grep -rn "sorry\|admit\|^axiom" KBFold SumFRI    # must print nothing
```

Afterwards (not part of this task): update the READMEs, `LEAN_MAP.md`, the KBFold paper's Lean
appendix and the Sum-FRI appendix (`sumfri/paper/sections/11-lean.tex`), which currently say that
`bciks_unique` is the only axiom.

## Status

(to be filled in by the agent)
