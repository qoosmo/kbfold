/-
KBFold/WordFold.lean
Formalisation of §5.3–5.4 of the paper: the kernel fold of a word (Definition 5.5),
its properties (Lemma 5.6), the line form (Lemma 5.7), consistency with the polynomial fold
(Proposition 5.8), folding a committed codeword (Corollary 5.9, together with the general
iterated form of Corollary 5.4), and the classical FRI fold (Definition 5.10,
Proposition 5.11).

Conventions as in `KBFold/Domain.lean`: `L : Subgroup Fˣ`, words are `L → F`, `-1 ∈ L`
and `(2 : F) ≠ 0` are explicit hypotheses where used (both follow from `L` being a smooth domain
of order `≥ 2`, see `IsSmoothDomain.neg_one_mem`, `two_ne_zero_of_smooth`).
Challenge sequences are functions `r : ℕ → F`; folding uses `r 0, r 1, …` in this order
(`r 0` is the paper's `r_1`).
-/
import KBFold.Domain

open Polynomial

namespace KBFold

variable {F : Type*} [Field F]

section WordFold

variable {L : Subgroup Fˣ}

/-- Definition 5.5: the kernel fold of a word, `fold_r(w) = (2r-1) w_e + (1-r) w_o ∈ F^{L²}`. -/
noncomputable def wfold (r : F) (w : L → F) : sqDom L → F :=
  fun η => (2 * r - 1) * evenW w η + (1 - r) * oddW w η

/-- Lemma 5.6(1) (explicit formula):
`fold_r(w)(ξ²) = (((2r-1)ξ + (1-r)) w(ξ) + ((2r-1)ξ - (1-r)) w(-ξ)) / (2ξ)`. -/
theorem wfold_sqPt (hL : (-1 : Fˣ) ∈ L) (h2 : (2 : F) ≠ 0) (r : F) (w : L → F) (ξ : L) :
    wfold r w (sqPt ξ) =
      (((2 * r - 1) * xv ξ + (1 - r)) * w ξ + ((2 * r - 1) * xv ξ - (1 - r)) * w (negPt ξ))
        / (2 * xv ξ) := by
  unfold wfold
  rw [evenW_sqPt hL, oddW_sqPt hL]
  have hξ : xv ξ ≠ 0 := Units.ne_zero _
  field_simp
  ring

/-- Lemma 5.6(2) (linearity): `fold_r` as an `F`-linear map `F^L → F^{L²}`. -/
noncomputable def wfoldLin (L : Subgroup Fˣ) (r : F) : (L → F) →ₗ[F] (sqDom L → F) :=
  (2 * r - 1) • evenLin L + (1 - r) • oddLin L

@[simp] theorem wfoldLin_apply (r : F) (w : L → F) : wfoldLin L r w = wfold r w := by
  funext η; simp [wfoldLin, wfold]

/-- Lemma 5.6(2): `fold_r(w + w') = fold_r(w) + fold_r(w')`. -/
theorem wfold_add (r : F) (w w' : L → F) : wfold r (w + w') = wfold r w + wfold r w' := by
  rw [← wfoldLin_apply, map_add]; simp

/-- Lemma 5.6(2): `fold_r(a w) = a fold_r(w)`. -/
theorem wfold_smul (r a : F) (w : L → F) : wfold r (a • w) = a • wfold r w := by
  rw [← wfoldLin_apply, map_smul]; simp

/-- Lemma 5.6(2): `fold_r(w - w') = fold_r(w) - fold_r(w')`. -/
theorem wfold_sub (r : F) (w w' : L → F) : wfold r (w - w') = wfold r w - wfold r w' := by
  rw [← wfoldLin_apply, map_sub]; simp

/-- Lemma 5.6(3) (locality): `fold_r(w)(η)` depends only on the values of `w` on the fibre
over `η`. -/
theorem wfold_congr (r : F) {w w' : L → F} {η : sqDom L} (h : ∀ ξ ∈ fibre η, w ξ = w' ξ) :
    wfold r w η = wfold r w' η := by
  unfold wfold; rw [evenW_congr h, oddW_congr h]

/-- Lemma 5.6(3), two-query form: `fold_r(w)(ξ²)` is determined by `w(ξ)` and `w(-ξ)`. -/
theorem wfold_congr_pair (hL : (-1 : Fˣ) ∈ L) (r : F) {w w' : L → F} (ξ : L)
    (h1 : w ξ = w' ξ) (h2 : w (negPt ξ) = w' (negPt ξ)) :
    wfold r w (sqPt ξ) = wfold r w' (sqPt ξ) := by
  apply wfold_congr
  intro ζ hζ
  rw [fibre_sqPt hL] at hζ
  rcases hζ with rfl | rfl
  · exact h1
  · exact h2

/-! ### Lemma 5.7 (line form) -/

/-- Lemma 5.7: `u⁰ = w_o - w_e`. -/
noncomputable def lineU0 (w : L → F) : sqDom L → F := oddW w - evenW w

/-- Lemma 5.7: `u¹ = 2 w_e - w_o`. -/
noncomputable def lineU1 (w : L → F) : sqDom L → F := 2 • evenW w - oddW w

/-- Lemma 5.7: `fold_r(w) = u⁰ + r u¹` for every `r`. -/
theorem wfold_line (r : F) (w : L → F) : wfold r w = lineU0 w + r • lineU1 w := by
  funext η; simp [wfold, lineU0, lineU1]; ring

/-- Lemma 5.7 (converse): `w_e = u⁰ + u¹`. -/
theorem evenW_line (w : L → F) : evenW w = lineU0 w + lineU1 w := by
  funext η; simp [lineU0, lineU1]; ring

/-- Lemma 5.7 (converse): `w_o = 2u⁰ + u¹`. -/
theorem oddW_line (w : L → F) : oddW w = 2 • lineU0 w + lineU1 w := by
  funext η; simp [lineU0, lineU1]; ring

/-! ### Proposition 5.8 (consistency with the polynomial fold) -/

/-- Proposition 5.8: `fold_r(ev_L(U)) = ev_{L²}(pfold_r(U))` (for every polynomial `U`; the
degree bound of the paper is only needed for the statements about codes). -/
theorem wfold_ev (hL : (-1 : Fˣ) ∈ L) (h2 : (2 : F) ≠ 0) (r : F) (U : F[X]) :
    wfold r (ev L U) = ev (sqDom L) (pfold r U) := by
  funext η
  simp only [wfold, evenW_ev hL h2, oddW_ev hL h2, pfold, ev, eval_add, eval_mul, eval_C]

/-- Definition 5.2: `pfold_r` maps `F[X]_{<2d}` into `F[X]_{<d}`. -/
theorem pfold_mem_degreeLT (r : F) {d : ℕ} {U : F[X]} (hU : U ∈ degreeLT F (2 * d)) :
    pfold r U ∈ degreeLT F d := by
  unfold pfold
  refine Submodule.add_mem _ ?_ ?_
  · rw [← smul_eq_C_mul]; exact Submodule.smul_mem _ _ (evenPart_mem_degreeLT hU)
  · rw [← smul_eq_C_mul]; exact Submodule.smul_mem _ _ (oddPart_mem_degreeLT hU)

/-- Proposition 5.8: `fold_r` maps `RS[L,2d]` into `RS[L²,d]`. -/
theorem wfold_mem_RS (hL : (-1 : Fˣ) ∈ L) (h2 : (2 : F) ≠ 0) (r : F) {d : ℕ} {c : L → F}
    (hc : c ∈ RS L (2 * d)) : wfold r c ∈ RS (sqDom L) d := by
  obtain ⟨U, hU, rfl⟩ := mem_RS.1 hc
  rw [wfold_ev hL h2]
  exact ev_mem_RS (pfold_mem_degreeLT r hU)

/-- Proposition 5.8: `P_{fold_r(c)} = pfold_r(P_c)` for `c ∈ RS[L,2d]`, when `2d ≤ |L|` and
`d ≤ |L²|` (the paper's hypothesis `1 ≤ d ≤ M/2` gives both). -/
theorem polyOf_wfold [Finite L] [Finite (sqDom L)] (hL : (-1 : Fˣ) ∈ L) (h2 : (2 : F) ≠ 0)
    (r : F) {d : ℕ} (hd : 2 * d ≤ Nat.card L) (hd' : d ≤ Nat.card (sqDom L)) {c : L → F}
    (hc : c ∈ RS L (2 * d)) : polyOf (wfold r c) = pfold r (polyOf c) := by
  obtain ⟨hP, hPc⟩ := polyOf_spec hd hc
  apply polyOf_unique hd' (pfold_mem_degreeLT r hP)
  rw [← wfold_ev hL h2, hPc]

/-! ### Iterated folds (Corollaries 5.4 and 5.9) -/

/-- Shift of a challenge sequence: `(r 1, r 2, …)`. -/
def shiftSeq (r : ℕ → F) : ℕ → F := fun i => r (i + 1)

/-- Iterated polynomial fold `U_j = pfold_{r_j}(⋯ pfold_{r_1}(U))` (Corollary 5.4), with the
challenges `r 0, …, r (j-1)`. -/
noncomputable def pfoldSeq : ℕ → (ℕ → F) → F[X] → F[X]
  | 0, _, U => U
  | j + 1, r, U => pfoldSeq j (shiftSeq r) (pfold (r 0) U)

/-- Iterated word fold `w_j = fold_{r_j}(⋯ fold_{r_1}(w))` (Corollary 5.9), a word on
`iterDom j L = L^{2^j}`. -/
noncomputable def wfoldSeq : (j : ℕ) → {L : Subgroup Fˣ} → (ℕ → F) → (L → F) → (iterDom j L → F)
  | 0, _, _, w => w
  | j + 1, _, r, w => wfoldSeq j (shiftSeq r) (wfold (r 0) w)

/-- Iterated restriction `res_{r ≤ j}(λ)` (Definition 2.10) of a table with `m + j` variables:
restrict the first variable at `r 0`, then the new first variable at `r 1`, and so on. -/
def resSeq : (j : ℕ) → {m : ℕ} → (ℕ → F) → Table F (m + j) → Table F m
  | 0, _, _, f => f
  | j + 1, _, r, f => resSeq j (shiftSeq r) (res (r 0) f)

/-- The point `(r_1, …, r_j, y_1, …, y_m)` of `F^{m+j}` (§2.1, "Points"). -/
def catPt : (j : ℕ) → {m : ℕ} → (ℕ → F) → (Fin m → F) → (Fin (m + j) → F)
  | 0, _, _, y => y
  | j + 1, _, r, y => Fin.cons (r 0) (catPt j (shiftSeq r) y)

/-- Lemma 2.11(2): `res_{r≤j}(λ)~(y) = λ~(r_1, …, r_j, y)`. -/
theorem mle_resSeq : ∀ (j : ℕ) {m : ℕ} (r : ℕ → F) (f : Table F (m + j)) (y : Fin m → F),
    mle (resSeq j r f) y = mle f (catPt j r y)
  | 0, _, _, _, _ => rfl
  | j + 1, _, r, f, y => by
      simp only [resSeq, catPt]
      rw [mle_resSeq j (shiftSeq r) (res (r 0) f) y, mle_res]

/-- Lemma 2.11(2), pointwise: `res_{r≤j}(λ)(b) = λ~(r_{≤j}, b)`. -/
theorem resSeq_eq_mle {j m : ℕ} (r : ℕ → F) (f : Table F (m + j)) (b : Fin m → Bool) :
    resSeq j r f b = mle f (catPt j r (pt b)) := by
  rw [← mle_resSeq, mle_pt]

/-- Corollary 5.4 (all `j`): the kernel coordinates of `U_j` are `res_{r≤j}(λ)`, i.e.
`U_j = ∑_b λ~(r_{≤j}, b) K_b^{(n-j)}`. -/
theorem pfoldSeq_ofCoords : ∀ (j : ℕ) {m : ℕ} (r : ℕ → F) (lam : Table F (m + j)),
    pfoldSeq j r (ofCoords lam) = ofCoords (resSeq j r lam)
  | 0, _, _, _ => rfl
  | j + 1, _, r, lam => by
      simp only [pfoldSeq, resSeq]
      rw [fold_dictionary, pfoldSeq_ofCoords j (shiftSeq r) (res (r 0) lam)]

/-- Corollary 5.4: after `n` folds, `U_n` is the constant `λ~(r_1, …, r_n)`. -/
theorem pfoldSeq_ofCoords_full (n : ℕ) (r : ℕ → F) (lam : Table F (0 + n)) :
    pfoldSeq n r (ofCoords lam) = C (mle lam (catPt n r Fin.elim0)) := by
  rw [pfoldSeq_ofCoords, ofCoords_zero_vars, ← mle_resSeq]
  congr 1
  unfold mle eqv
  rw [Fintype.sum_unique]
  simp only [Finset.univ_eq_empty, Finset.prod_empty, mul_one]
  exact congrArg _ (Subsingleton.elim _ _)

/-- Consistency of the iterated word fold with the iterated polynomial fold: if
`-1 ∈ L^{2^i}` for all `i < j`, then `w_j = ev_{L^{2^j}}(U_j)` for `w_0 = ev_L(U)`. -/
theorem wfoldSeq_ev (h2 : (2 : F) ≠ 0) :
    ∀ (j : ℕ) {L : Subgroup Fˣ} (r : ℕ → F) (U : F[X]),
      (∀ i < j, (-1 : Fˣ) ∈ iterDom i L) →
      wfoldSeq j r (ev L U) = ev (iterDom j L) (pfoldSeq j r U)
  | 0, _, _, _, _ => rfl
  | j + 1, L, r, U, hneg => by
      simp only [wfoldSeq, pfoldSeq]
      rw [wfold_ev (show (-1 : Fˣ) ∈ L from hneg 0 (Nat.succ_pos _)) h2]
      exact wfoldSeq_ev h2 j (shiftSeq r) (pfold (r 0) U)
        (fun i hi => hneg (i + 1) (by omega))

/-- In a smooth domain of order `2^μ`, `-1 ∈ L^{2^i}` for every `i < μ`. -/
theorem IsSmoothDomain.neg_one_mem_iterDom {L : Subgroup Fˣ} {μ : ℕ} (hL : IsSmoothDomain L μ)
    {i : ℕ} (hi : i < μ) : (-1 : Fˣ) ∈ iterDom i L :=
  (hL.iterDom_smooth hi.le).neg_one_mem (by omega)

/-- Corollary 5.9 (folding a committed codeword): let `L` be a smooth domain of order `2^μ`,
`λ` a table with `n = m + j` variables where `j ≤ μ`, and `w_0 = ev_L(∑_b λ(b) K_b)`.  Then the
`j`-th fold is `w_j = ev_{L^{2^j}}(U_j)` with `U_j = ∑_b res_{r≤j}(λ)(b) K_b`
(whose coefficients are `λ~(r_{≤j}, b)` by `resSeq_eq_mle`). -/
theorem codeword_fold {L : Subgroup Fˣ} {μ : ℕ} (hL : IsSmoothDomain L μ) {j m : ℕ}
    (hj : j ≤ μ) (r : ℕ → F) (lam : Table F (m + j)) :
    wfoldSeq j r (ev L (ofCoords lam)) = ev (iterDom j L) (ofCoords (resSeq j r lam)) := by
  rcases Nat.eq_zero_or_pos j with rfl | hpos
  · rfl
  rw [wfoldSeq_ev (two_ne_zero_of_smooth hL (by omega)) j r _
    (fun i hi => hL.neg_one_mem_iterDom (by omega)), pfoldSeq_ofCoords]

/-- Corollary 5.9, last statement: with `n ≤ μ` variables (and `n ≥ 1`), `w_n` is the constant
word on `L^{2^n}` with value `λ~(r_1, …, r_n)`. -/
theorem codeword_fold_full {L : Subgroup Fˣ} {μ n : ℕ} (hL : IsSmoothDomain L μ) (hn : n ≤ μ)
    (hn1 : 1 ≤ n) (r : ℕ → F) (lam : Table F (0 + n)) :
    wfoldSeq n r (ev L (ofCoords lam)) = fun _ => mle lam (catPt n r Fin.elim0) := by
  rw [wfoldSeq_ev (two_ne_zero_of_smooth hL (by omega)) n r _
    (fun i hi => hL.neg_one_mem_iterDom (by omega)), pfoldSeq_ofCoords_full]
  funext η; simp [ev]

/-! ### Definition 5.10 and Proposition 5.11 (classical FRI fold) -/

/-- Definition 5.10: the classical FRI fold of a polynomial, `cfold_θ(U) = U_e + θ U_o`. -/
noncomputable def cfold (θ : F) (U : F[X]) : F[X] := evenPart U + C θ * oddPart U

/-- Definition 5.10: the classical FRI fold of a word, `cfold_θ(w) = w_e + θ w_o`. -/
noncomputable def cwfold (θ : F) (w : L → F) : sqDom L → F := evenW w + θ • oddW w

/-- Proposition 5.11(1): the kernel coordinates of `cfold_θ(U)` are
`b' ↦ θ λ(2b') + (1+θ) λ(2b'+1)`. -/
theorem cfold_ofCoords {n : ℕ} (θ : F) (lam : Table F (n + 1)) :
    cfold θ (ofCoords lam) =
      ofCoords (fun b' => θ * lam (Fin.cons false b') + (1 + θ) * lam (Fin.cons true b')) := by
  unfold cfold
  rw [evenPart_ofCoords, oddPart_ofCoords, ← ofCoords_smul, ← ofCoords_add]
  congr 1; funext b'; simp only [Pi.add_apply]; ring

/-- Proposition 5.11(2): if `1 + 2θ ≠ 0` then `cfold_θ = (1+2θ) pfold_r` with
`r = (1+θ)/(1+2θ)`. -/
theorem cfold_eq_pfold (θ : F) (hθ : 1 + 2 * θ ≠ 0) (U : F[X]) :
    cfold θ U = C (1 + 2 * θ) * pfold ((1 + θ) / (1 + 2 * θ)) U := by
  unfold cfold pfold
  have e1 : (1 + 2 * θ) * (2 * ((1 + θ) / (1 + 2 * θ)) - 1) = 1 := by field_simp; ring
  have e2 : (1 + 2 * θ) * (1 - (1 + θ) / (1 + 2 * θ)) = θ := by field_simp; ring
  rw [mul_add, ← mul_assoc, ← mul_assoc, ← C_mul, ← C_mul, e1, e2, C_1, one_mul]

/-- Proposition 5.11(2), converse: if `2r - 1 ≠ 0` then `pfold_r = (2r-1) cfold_θ` with
`θ = (1-r)/(2r-1)`. -/
theorem pfold_eq_cfold (r : F) (hr : 2 * r - 1 ≠ 0) (U : F[X]) :
    pfold r U = C (2 * r - 1) * cfold ((1 - r) / (2 * r - 1)) U := by
  unfold cfold pfold
  have e2 : (2 * r - 1) * ((1 - r) / (2 * r - 1)) = 1 - r := by field_simp
  rw [mul_add, ← mul_assoc, ← C_mul, e2]

/-- Iterated classical fold with challenges `θ 0, θ 1, …`. -/
noncomputable def cfoldSeq : ℕ → (ℕ → F) → F[X] → F[X]
  | 0, _, U => U
  | j + 1, θ, U => cfoldSeq j (shiftSeq θ) (cfold (θ 0) U)

lemma pfold_C_mul (r a : F) (U : F[X]) : pfold r (C a * U) = C a * pfold r U := by
  unfold pfold evenPart oddPart
  have h1 : contract 2 (C a * U) = C a * contract 2 U := by
    ext i; simp [coeff_contract two_ne_zero, coeff_C_mul]
  have h2 : contract 2 (divX (C a * U)) = C a * contract 2 (divX U) := by
    ext i; simp [coeff_contract two_ne_zero, coeff_divX, coeff_C_mul]
  rw [h1, h2]; ring

lemma pfoldSeq_C_mul : ∀ (j : ℕ) (r : ℕ → F) (a : F) (U : F[X]),
    pfoldSeq j r (C a * U) = C a * pfoldSeq j r U
  | 0, _, _, _ => rfl
  | j + 1, r, a, U => by
      simp only [pfoldSeq]; rw [pfold_C_mul, pfoldSeq_C_mul j]

/-- Proposition 5.11(3): if `1 + 2θ_i ≠ 0` for all `i < j`, successive classical folds equal
`∏ (1+2θ_i)` times successive kernel folds with `r_i = (1+θ_i)/(1+2θ_i)`; for `j = n` this is
`∏ (1+2θ_i) · λ~(r_1, …, r_n)` by `pfoldSeq_ofCoords_full`. -/
theorem cfoldSeq_eq : ∀ (j : ℕ) (θ : ℕ → F) (U : F[X]), (∀ i < j, 1 + 2 * θ i ≠ 0) →
    cfoldSeq j θ U = C (∏ i ∈ Finset.range j, (1 + 2 * θ i)) *
      pfoldSeq j (fun i => (1 + θ i) / (1 + 2 * θ i)) U
  | 0, _, U, _ => by simp [cfoldSeq, pfoldSeq]
  | j + 1, θ, U, h => by
      simp only [cfoldSeq, pfoldSeq]
      rw [cfoldSeq_eq j (shiftSeq θ) _ (fun i hi => h (i + 1) (by omega)),
        cfold_eq_pfold _ (h 0 (by omega)), pfoldSeq_C_mul, ← mul_assoc, ← C_mul,
        Finset.prod_range_succ']
      rfl

/-- Proposition 5.11(3): for `λ` with `n` variables and `1 + 2θ_i ≠ 0`, the `n`-fold classical
fold is the constant `∏ (1+2θ_i) · λ~((1+θ_1)/(1+2θ_1), …)`. -/
theorem cfoldSeq_ofCoords (n : ℕ) (θ : ℕ → F) (lam : Table F (0 + n))
    (h : ∀ i < n, 1 + 2 * θ i ≠ 0) :
    cfoldSeq n θ (ofCoords lam) = C ((∏ i ∈ Finset.range n, (1 + 2 * θ i)) *
      mle lam (catPt n (fun i => (1 + θ i) / (1 + 2 * θ i)) Fin.elim0)) := by
  rw [cfoldSeq_eq n θ _ h, pfoldSeq_ofCoords_full, C_mul]

/-- Proposition 5.11(4), one step: `cfold_ζ(U)(ζ²) = U(ζ)` for every `U` and `ζ`. -/
theorem cfold_eval (U : F[X]) (ζ : F) : (cfold ζ U).eval (ζ ^ 2) = U.eval ζ := by
  rw [eval_even_odd U ζ, cfold]; simp

/-- Proposition 5.11(4), evaluation form: folding with `θ_j = ζ^{2^{j-1}}`, `j = 1..n`, gives a
polynomial whose value at `ζ^{2^n}` is `U(ζ)` (for every polynomial `U`). -/
theorem cfoldSeq_pow_eval : ∀ (j : ℕ) (ζ : F) (U : F[X]),
    (cfoldSeq j (fun i => ζ ^ (2 ^ i)) U).eval (ζ ^ (2 ^ j)) = U.eval ζ
  | 0, ζ, U => by simp [cfoldSeq]
  | j + 1, ζ, U => by
      simp only [cfoldSeq]
      have hs : shiftSeq (fun i => ζ ^ (2 ^ i)) = fun i => (ζ ^ 2) ^ (2 ^ i) := by
        funext i; simp only [shiftSeq]; rw [← pow_mul, ← pow_succ']
      have hp : ζ ^ (2 ^ (j + 1)) = (ζ ^ 2) ^ (2 ^ j) := by rw [← pow_mul, ← pow_succ']
      rw [hs, hp, cfoldSeq_pow_eval j (ζ ^ 2), pow_zero, pow_one, cfold_eval]

/-- Definition 5.10: `cfold_θ` maps `F[X]_{<2d}` into `F[X]_{<d}`. -/
theorem cfold_mem_degreeLT (θ : F) {d : ℕ} {U : F[X]} (hU : U ∈ degreeLT F (2 * d)) :
    cfold θ U ∈ degreeLT F d := by
  unfold cfold
  refine Submodule.add_mem _ (evenPart_mem_degreeLT hU) ?_
  rw [← smul_eq_C_mul]; exact Submodule.smul_mem _ _ (oddPart_mem_degreeLT hU)

theorem cfoldSeq_mem_degreeLT : ∀ (j : ℕ) (θ : ℕ → F) {d : ℕ} {U : F[X]},
    U ∈ degreeLT F (2 ^ j * d) → cfoldSeq j θ U ∈ degreeLT F d
  | 0, _, _, _, hU => by simpa [cfoldSeq] using hU
  | j + 1, θ, d, U, hU => by
      simp only [cfoldSeq]
      apply cfoldSeq_mem_degreeLT j
      apply cfold_mem_degreeLT
      have : 2 * (2 ^ j * d) = 2 ^ (j + 1) * d := by ring
      rw [this]; exact hU

/-- Proposition 5.11(4): for `U ∈ F[X]_{<2^n}`, folding with `θ_j = ζ^{2^{j-1}}` gives the
constant `U(ζ)`. -/
theorem cfoldSeq_pow_const (n : ℕ) (ζ : F) {U : F[X]} (hU : U ∈ degreeLT F (2 ^ n)) :
    cfoldSeq n (fun i => ζ ^ (2 ^ i)) U = C (U.eval ζ) := by
  have h1 := cfoldSeq_mem_degreeLT n (fun i => ζ ^ (2 ^ i)) (d := 1) (by simpa using hU)
  rw [mem_degreeLT, Nat.cast_one, Nat.WithBot.lt_one_iff_le_zero] at h1
  have h3 := cfoldSeq_pow_eval n ζ U
  set p := cfoldSeq n (fun i => ζ ^ (2 ^ i)) U with hp
  rw [eq_C_of_degree_le_zero h1, eval_C] at h3
  rw [eq_C_of_degree_le_zero h1, h3]

end WordFold

end KBFold
