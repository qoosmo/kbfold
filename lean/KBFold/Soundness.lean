/-
KBFold/Soundness.lean
§7.3–7.5 of the paper: passing sets (Lemma 7.11), the codeword chain (Lemma 7.12), the soundness
theorem (Theorem 7.13), evaluation binding (Corollary 7.14) and the case `ℓ = 0`
(Proposition 7.15).

Setting (see `KBFold/Protocol.lean` for the modelling of `Π_eval`).
* `n = m + ℓ` variables, `1 ≤ ℓ`; `L` is a smooth domain of order `M = 2^{n+R}`;
  `N_j = 2^{n-j}` (`Nd m ℓ j`), `L_j = lv L j` of order `M_j = 2^{n+R-j}`, and the codes
  `𝒞_j = RS[L_j, N_j]`, all of rate `ρ = 2^{-R}` (`rate_lv`).
* `0 < δ ≤ (1-ρ)/2`.
* For a level `j < ℓ` the code `𝒞_j` is written `RS (lv L j) (2 * N_{j+1})` (`N_j = 2 N_{j+1}`,
  `Nd_succ`), which is the form used by the one-step lemmas of `KBFold/Fibre.lean`.
* A fixed deterministic prover `P : EvalProver F L m` (messages as functions of the challenges),
  causal and with round polynomials of degree `≤ 2`, and an instance `(w₀; z, v)` with
  `z = catPt ℓ zp zs`.
-/
import KBFold.Completeness
import KBFold.RoundByRound

set_option autoImplicit false

open Polynomial Finset

namespace KBFold

variable {F : Type*} [Field F]

/-! ### Parameters of the levels -/

section Params

variable {L : Subgroup Fˣ} {m ℓ R : ℕ}

/-- The degree bound `N_j = 2^{n-j}` (with `n = m + ℓ`). -/
def Nd (m ℓ j : ℕ) : ℕ := 2 ^ (m + ℓ - j)

lemma Nd_pos (m ℓ j : ℕ) : 1 ≤ Nd m ℓ j := Nat.one_le_two_pow

/-- `N_j = 2 N_{j+1}` for `j < n`. -/
lemma Nd_succ {j : ℕ} (hj : j < m + ℓ) : 2 * Nd m ℓ (j + 1) = Nd m ℓ j := by
  unfold Nd
  rw [← pow_succ']; congr 1; omega

lemma Nd_last : Nd m ℓ ℓ = 2 ^ m := by unfold Nd; congr 1; omega

lemma Nd_zero : Nd m ℓ 0 = 2 ^ (m + ℓ) := rfl

/-- `|L_j| = M_j = 2^{n+R-j}`. -/
lemma card_lv (hL : IsSmoothDomain L (m + ℓ + R)) {j : ℕ} (hj : j ≤ m + ℓ + R) :
    Nat.card (lv L j) = 2 ^ (m + ℓ + R - j) :=
  lv_smooth hL hj

/-- All the codes `𝒞_j` have rate `ρ = 2^{-R}`. -/
lemma rate_lv (hL : IsSmoothDomain L (m + ℓ + R)) {j : ℕ} (hj : j ≤ m + ℓ) :
    rate (lv L j) (Nd m ℓ j) = 1 / 2 ^ R := by
  rw [rate, card_lv hL (by omega), Nd]
  have : m + ℓ + R - j = (m + ℓ - j) + R := by omega
  rw [this, pow_add]
  push_cast
  field_simp

lemma Nd_le_card (hL : IsSmoothDomain L (m + ℓ + R)) {j : ℕ} (hj : j ≤ m + ℓ) :
    Nd m ℓ j ≤ Nat.card (lv L j) := by
  rw [card_lv hL (by omega), Nd]
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

/-- `|L_j| = 2 |L_{j+1}|` for `j < n + R`. -/
lemma card_lv_succ (hL : IsSmoothDomain L (m + ℓ + R)) {j : ℕ} (hj : j < m + ℓ + R) :
    Nat.card (lv L j) = 2 * Nat.card (lv L (j + 1)) := by
  rw [card_lv hL hj.le, card_lv hL hj, ← pow_succ']; congr 1; omega

end Params

/-! ### Passing sets (Lemma 7.11) -/

section Passing

variable {L : Subgroup Fˣ} {m : ℕ} (P : EvalProver F L m) (ℓ : ℕ) (w0 : L → F)

/-- **Passing sets** (§7.3): `𝒫_j ⊆ L_j` is the set of points `ξ_j = ξ₀^{2^j}` for which the
query checks at levels `j+1, …, ℓ` pass.  (The paper defines `𝒫_j` by downward recursion; the
recursion is `mem_Pass_iff`, and Lemma 7.11(1) is `ptAt_mem_Pass`.) -/
def Pass (r : ℕ → F) (j : ℕ) : Set (lv L j) :=
  {η | ∃ ξ : L, ptAt ξ j = η ∧ ∀ i, j ≤ i → i < ℓ → P.Chk ℓ w0 r i (ptAt ξ (i + 1))}

variable {P ℓ w0}

/-- **Lemma 7.11(1):** `ξ₀^{2^j} ∈ 𝒫_j` iff the query checks at levels `j+1, …, ℓ` pass
for `ξ₀`. -/
theorem ptAt_mem_Pass (r : ℕ → F) (j : ℕ) (ξ : L) :
    ptAt ξ j ∈ Pass P ℓ w0 r j ↔ ∀ i, j ≤ i → i < ℓ → P.Chk ℓ w0 r i (ptAt ξ (i + 1)) := by
  constructor
  · rintro ⟨ξ', he, h⟩ i hji hi
    rw [← ptAt_congr he (i + 1) (by omega)]
    exact h i hji hi
  · intro h; exact ⟨ξ, rfl, h⟩

/-- **Lemma 7.11(1), `j = 0`:** `ξ₀` passes all the query checks iff `ξ₀ ∈ 𝒫_0`. -/
theorem mem_Pass_zero (r : ℕ → F) (ξ : L) :
    ξ ∈ Pass P ℓ w0 r 0 ↔ ∀ i < ℓ, P.Chk ℓ w0 r i (ptAt ξ (i + 1)) := by
  have := ptAt_mem_Pass (P := P) (ℓ := ℓ) (w0 := w0) r 0 ξ
  simp only [zero_le, true_implies] at this
  exact this

/-- The recursive definition of the passing sets (§7.3): `𝒫_ℓ = L_ℓ` and, for `j < ℓ`,
`𝒫_j = {ξ ∈ L_j : ξ² ∈ 𝒫_{j+1} ∧ fold_{r_{j+1}}(w_j)(ξ²) = w_{j+1}(ξ²)}`. -/
theorem mem_Pass_iff (r : ℕ → F) {j : ℕ} (hj : j < ℓ) (η : lv L j) :
    η ∈ Pass P ℓ w0 r j ↔ sqPt η ∈ Pass P ℓ w0 r (j + 1) ∧ P.Chk ℓ w0 r j (sqPt η) := by
  obtain ⟨ξ, rfl⟩ := ptAt_surjective j η
  have e : sqPt (ptAt ξ j) = ptAt ξ (j + 1) := rfl
  rw [e, ptAt_mem_Pass, ptAt_mem_Pass]
  constructor
  · intro h
    exact ⟨fun i hi hiℓ => h i (by omega) hiℓ, h j le_rfl hj⟩
  · rintro ⟨h1, h2⟩ i hi hiℓ
    rcases Nat.eq_or_lt_of_le hi with rfl | hlt
    · exact h2
    · exact h1 i hlt hiℓ

theorem Pass_last (r : ℕ → F) : Pass P ℓ w0 r ℓ = Set.univ := by
  ext η
  obtain ⟨ξ, rfl⟩ := ptAt_surjective ℓ η
  simp only [Set.mem_univ, iff_true]
  exact ⟨ξ, rfl, fun i h1 h2 => absurd h2 (by omega)⟩

/-- **Lemma 7.11(2):** for `j < ℓ`, `𝒫_j` is a union of fibres ... -/
theorem Pass_neg (r : ℕ → F) {j : ℕ} (hj : j < ℓ)
    (η : lv L j) (hη : η ∈ Pass P ℓ w0 r j) : negPt η ∈ Pass P ℓ w0 r j := by
  rw [mem_Pass_iff r hj] at hη ⊢
  rwa [sqPt_negPt]

/-- **Lemma 7.11(2):** ... and squaring maps it into `𝒫_{j+1}`. -/
theorem sq_Pass_subset (r : ℕ → F) {j : ℕ} (hj : j < ℓ) :
    sqPt '' Pass P ℓ w0 r j ⊆ Pass P ℓ w0 r (j + 1) := by
  rintro _ ⟨η, hη, rfl⟩
  exact ((mem_Pass_iff r hj η).1 hη).1

/-- The fraction `π(r) = |𝒫_0| / M` of passing query points (§7.3). -/
noncomputable def passFrac (r : ℕ → F) : ℚ := ((Pass P ℓ w0 r 0).ncard : ℚ) / Nat.card L

/-- **Lemma 7.11(2)–(3)**, halving step: `|𝒫_j²| = |𝒫_j|/2`, so `|𝒫_j| ≥ π M_j` implies
`|𝒫_j²| ≥ π M_{j+1}`. -/
theorem Pass_card_step {R : ℕ} (hL : IsSmoothDomain L (m + ℓ + R)) (r : ℕ → F) (j : ℕ)
    (hj : j < ℓ) (h : passFrac (P := P) (ℓ := ℓ) (w0 := w0) r * Nat.card (lv L j)
        ≤ (Pass P ℓ w0 r j).ncard) :
    passFrac (P := P) (ℓ := ℓ) (w0 := w0) r * Nat.card (lv L (j + 1))
      ≤ (sqPt '' Pass P ℓ w0 r j).ncard := by
  haveI := hL.finite
  haveI := lv_finite (L := L) j
  have hneg := lv_neg_one_mem hL (j := j) (by omega)
  have h2F := two_ne_zero_of_smooth hL (by omega : 1 ≤ m + ℓ + R)
  have hc := ncard_eq_two_mul_image hneg h2F (Pass P ℓ w0 r j)
    (fun η hη => Pass_neg r hj η hη)
  have hM := card_lv_succ hL (j := j) (by omega)
  rw [hc, hM] at h
  push_cast at h
  linarith

/-- **Lemma 7.11(3):** `|𝒫_j| ≥ π M_j` for every `j ≤ ℓ`. -/
theorem Pass_card {R : ℕ} (hL : IsSmoothDomain L (m + ℓ + R)) (r : ℕ → F) :
    ∀ j ≤ ℓ, passFrac (P := P) (ℓ := ℓ) (w0 := w0) r * Nat.card (lv L j)
        ≤ (Pass P ℓ w0 r j).ncard
  | 0, _ => by
      haveI := hL.finite
      have hpos : (0 : ℚ) < Nat.card L := by
        haveI : Nonempty L := ⟨1⟩; exact_mod_cast Nat.card_pos
      have e : Nat.card (lv L 0) = Nat.card L := rfl
      rw [e, passFrac, div_mul_cancel₀ _ hpos.ne']
  | j + 1, hj => by
      haveI := hL.finite
      haveI := lv_finite (L := L) (j + 1)
      refine (Pass_card_step hL r j (by omega) (Pass_card hL r j (by omega))).trans ?_
      have := Set.ncard_le_ncard (sq_Pass_subset (P := P) (w0 := w0) r (j := j) (by omega))
        (Set.toFinite (Pass P ℓ w0 r (j + 1)))
      exact_mod_cast this

/-- **Lemma 7.11(2)–(3):** `|𝒫_j²| ≥ π M_{j+1}` for `j < ℓ` (used in Lemma 7.12). -/
theorem sq_Pass_card {R : ℕ} (hL : IsSmoothDomain L (m + ℓ + R)) (r : ℕ → F) {j : ℕ}
    (hj : j < ℓ) : passFrac (P := P) (ℓ := ℓ) (w0 := w0) r * Nat.card (lv L (j + 1))
      ≤ (sqPt '' Pass P ℓ w0 r j).ncard :=
  Pass_card_step hL r j hj (Pass_card hL r j hj.le)

end Passing

/-! ### The oracle words -/

section Words

variable {L : Subgroup Fˣ} {m : ℕ} (P : EvalProver F L m) {ℓ : ℕ} (w0 : L → F)

lemma W_zero (r : ℕ → F) : P.W ℓ w0 r 0 = w0 := rfl

/-- The last word `w_ℓ = ev_{L_ℓ}(G)`, `G = ∑_b g(b) K_b^{(n-ℓ)}`. -/
lemma W_last (hℓ : 1 ≤ ℓ) (r : ℕ → F) : P.W ℓ w0 r ℓ = ev (lv L ℓ) (ofCoords (P.g r)) := by
  obtain ⟨k, rfl⟩ : ∃ k, ℓ = k + 1 := ⟨ℓ - 1, by omega⟩
  simp [EvalProver.W]

lemma W_mid {j : ℕ} (hj0 : 0 < j) (hj : j < ℓ) (r : ℕ → F) : P.W ℓ w0 r j = P.orc j r := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  simp only [EvalProver.W]
  rw [if_neg (by omega)]

/-- The words `w_j`, `j < ℓ`, depend only on `r_{<j}` (causality). -/
lemma W_congr (hC : P.Causal) {j : ℕ} (hj : j < ℓ) {r r' : ℕ → F}
    (h : ∀ k < j, r k = r' k) : P.W ℓ w0 r j = P.W ℓ w0 r' j := by
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · rfl
  · rw [W_mid P w0 hj0 hj, W_mid P w0 hj0 hj, hC.2 j r r' h]

lemma W_last_mem_RS (hℓ : 1 ≤ ℓ) (r : ℕ → F) : P.W ℓ w0 r ℓ ∈ RS (lv L ℓ) (Nd m ℓ ℓ) := by
  rw [W_last P w0 hℓ, Nd_last]; exact ev_mem_RS (ofCoords_mem_degreeLT _)

end Words

/-- A sequence of words `c_j` on the levels with `fold_{r_{j+1}}(c_j) = c_{j+1}` is the sequence
of successive folds of `c_0`. -/
lemma foldUp_of_chain {L : Subgroup Fˣ} {ℓ : ℕ} (r : ℕ → F) (c : (j : ℕ) → lv L j → F)
    (h : ∀ j < ℓ, wfold (r j) (c j) = c (j + 1)) : ∀ j ≤ ℓ, c j = foldUp r (c 0) j
  | 0, _ => rfl
  | j + 1, hj => by
      rw [foldUp, ← foldUp_of_chain r c h j (by omega), h j (by omega)]

/-! ### Lemma 7.12 (the codeword chain) -/

section Chain

variable {L : Subgroup Fˣ} {m : ℕ} (P : EvalProver F L m) (ℓ : ℕ) (w0 : L → F) (δ : ℚ)

/-- **Definition 7.8 at level `j+1`:** `r` is good for the word `w ∈ F^{L_j}`
(`Good` of `KBFold/Fibre.lean` with `𝒞_j = RS[L_j, 2N_{j+1}]`, `𝒞_{j+1} = RS[L_{j+1}, N_{j+1}]`). -/
def GoodAt (m : ℕ) (j : ℕ) (w : lv L j → F) (r : F) : Prop := Good δ (Nd m ℓ (j + 1)) w r

/-- **Definition 7.4 at level `j`:** `dec_j(w)`, for `w ∈ F^{L_j}`, `j < ℓ`. -/
noncomputable def decAt (m : ℕ) (j : ℕ) (w : lv L j → F) : lv L j → F :=
  dec (RS (lv L j) (2 * Nd m ℓ (j + 1)) : Set (lv L j → F)) δ w

/-- The codeword chain of Lemma 7.12: `c_j = dec_j(w_j)` for `j < ℓ` and `c_ℓ = w_ℓ`. -/
noncomputable def chainCw (r : ℕ → F) (j : ℕ) : lv L j → F :=
  if j < ℓ then decAt ℓ δ m j (P.W ℓ w0 r j) else P.W ℓ w0 r j

variable {P ℓ w0 δ}

/-- The fold lemmas of `KBFold/Fibre.lean` apply at every level `j < ℓ`. -/
lemma level_facts {R : ℕ} (hL : IsSmoothDomain L (m + ℓ + R)) {j : ℕ} (hj : j < ℓ) :
    IsSmoothDomain (lv L j) (m + ℓ + R - j) ∧ 1 ≤ m + ℓ + R - j ∧
      2 * Nd m ℓ (j + 1) ≤ Nat.card (lv L j) ∧
      rate (sqDom (lv L j)) (Nd m ℓ (j + 1)) = 1 / 2 ^ R :=
  ⟨lv_smooth hL (by omega), by omega, by rw [Nd_succ (by omega)]; exact Nd_le_card hL (by omega),
    rate_lv hL (j := j + 1) (by omega)⟩

/-- **Lemma 7.12 (the codeword chain).** Fix `r` such that `r_{j+1}` is good for `w_j` for every
`j < ℓ`, and `π(r) > 1-δ`.  Then `Δ^fib_j(w_j, 𝒞_j) ≤ δ` for every `j < ℓ`, and the codewords
`c_j = dec_j(w_j)` (`j < ℓ`), `c_ℓ = w_ℓ` satisfy `fold_{r_{j+1}}(c_j) = c_{j+1}` and
`w_j = c_j` on `𝒫_j`. -/
theorem chain {R : ℕ} (hL : IsSmoothDomain L (m + ℓ + R)) (hℓ : 1 ≤ ℓ)
    (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2) (r : ℕ → F)
    (hgood : ∀ j < ℓ, GoodAt ℓ δ m j (P.W ℓ w0 r j) (r j))
    (hπ : 1 - δ < passFrac (P := P) (ℓ := ℓ) (w0 := w0) r) :
    (∀ j < ℓ, FibDistLE (P.W ℓ w0 r j) (RS (lv L j) (2 * Nd m ℓ (j + 1)) : Set _) δ ∧
        wfold (r j) (chainCw P ℓ w0 δ r j) = chainCw P ℓ w0 δ r (j + 1)) ∧
      ∀ j ≤ ℓ, ∀ η ∈ Pass P ℓ w0 r j, P.W ℓ w0 r j η = chainCw P ℓ w0 δ r j η := by
  -- `Q j`: the claims at level `j`, proved by downward induction
  let Q : ℕ → Prop := fun j =>
    (j < ℓ → FibDistLE (P.W ℓ w0 r j) (RS (lv L j) (2 * Nd m ℓ (j + 1)) : Set _) δ ∧
        wfold (r j) (chainCw P ℓ w0 δ r j) = chainCw P ℓ w0 δ r (j + 1)) ∧
      ∀ η ∈ Pass P ℓ w0 r j, P.W ℓ w0 r j η = chainCw P ℓ w0 δ r j η
  have key : ∀ k j, j + k = ℓ → Q j := by
    intro k
    induction k with
    | zero =>
      intro j hj
      simp only [add_zero] at hj
      subst hj
      refine ⟨fun h => absurd h (lt_irrefl _), fun η _ => ?_⟩
      simp [chainCw]
    | succ k ih =>
      intro j hjk
      have hj : j < ℓ := by omega
      obtain ⟨ihF, ihP⟩ := ih (j + 1) (by omega)
      obtain ⟨hDj, hμj, hdD, hrate⟩ := level_facts hL hj
      have hδj : δ ≤ (1 - rate (sqDom (lv L j)) (Nd m ℓ (j + 1))) / 2 := by rw [hrate]; exact hδ
      haveI := hL.finite
      haveI : Finite (sqDom (lv L j)) := lv_finite (L := L) (j + 1)
      -- the next codeword `c_{j+1}` lies in `𝒞_{j+1}`
      have hc' : chainCw P ℓ w0 δ r (j + 1) ∈ RS (sqDom (lv L j)) (Nd m ℓ (j + 1)) := by
        by_cases hj1 : j + 1 < ℓ
        · have hF := (ihF hj1).1
          have hmem := (dec_spec hF).1
          simp only [chainCw, if_pos hj1, decAt]
          have e : 2 * Nd m ℓ (j + 1 + 1) = Nd m ℓ (j + 1) := Nd_succ (by omega)
          rw [e] at hmem ⊢
          exact hmem
        · have e : j + 1 = ℓ := by omega
          simp only [chainCw, if_neg hj1]
          have := W_last_mem_RS P w0 hℓ r
          subst e
          exact this
      -- `Y ⊇ 𝒫_j²`
      have hsub : sqPt '' Pass P ℓ w0 r j ⊆
          agreeSet (wfold (r j) (P.W ℓ w0 r j)) (chainCw P ℓ w0 δ r (j + 1)) := by
        rintro _ ⟨η, hη, rfl⟩
        obtain ⟨h1, h2⟩ := (mem_Pass_iff r hj η).1 hη
        show wfold (r j) (P.W ℓ w0 r j) (sqPt η) = chainCw P ℓ w0 δ r (j + 1) (sqPt η)
        rw [← ihP _ h1]
        exact h2
      have hY : (1 - δ) * Nat.card (sqDom (lv L j)) ≤
          (agreeSet (wfold (r j) (P.W ℓ w0 r j)) (chainCw P ℓ w0 δ r (j + 1))).ncard := by
        have h1 := sq_Pass_card (P := P) (w0 := w0) hL r hj
        have h2 : ((sqPt '' Pass P ℓ w0 r j).ncard : ℚ) ≤
            (agreeSet (wfold (r j) (P.W ℓ w0 r j)) (chainCw P ℓ w0 δ r (j + 1))).ncard := by
          exact_mod_cast Set.ncard_le_ncard hsub (Set.toFinite _)
        have h3 : (0 : ℚ) ≤ Nat.card (lv L (j + 1)) := Nat.cast_nonneg _
        have h4 : (1 - δ) * Nat.card (lv L (j + 1)) ≤
            passFrac (P := P) (ℓ := ℓ) (w0 := w0) r * Nat.card (lv L (j + 1)) :=
          mul_le_mul_of_nonneg_right hπ.le h3
        exact h4.trans (h1.trans h2)
      obtain ⟨hF, hfold, hagree⟩ := one_step hDj hμj hδj (P.W ℓ w0 r j) (r j) (hgood j hj) _ hc' hY
      have hcj : chainCw P ℓ w0 δ r j = dec (RS (lv L j) (2 * Nd m ℓ (j + 1)) : Set _) δ
          (P.W ℓ w0 r j) := by
        simp only [chainCw, if_pos hj, decAt]
      refine ⟨fun _ => ⟨hF, by rw [hcj]; exact hfold⟩, fun η hη => ?_⟩
      rw [hcj]
      exact hagree (sqPt η) (hsub ⟨η, hη, rfl⟩) η rfl
  refine ⟨fun j hj => (key (ℓ - j) j (by omega)).1 hj, fun j hj => (key (ℓ - j) j (by omega)).2⟩

/-- **Lemma 7.12, last claim:** under the hypotheses of `chain`, `Δ^fib₀(w₀, 𝒞₀) ≤ δ` and the
final table is `g = res_r(f*)`, where `f*` is the decoded table of `w₀`. -/
theorem chain_final {R : ℕ} (hL : IsSmoothDomain L (m + ℓ + R)) (hℓ : 1 ≤ ℓ)
    (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2) (r : ℕ → F)
    (hgood : ∀ j < ℓ, GoodAt ℓ δ m j (P.W ℓ w0 r j) (r j))
    (hπ : 1 - δ < passFrac (P := P) (ℓ := ℓ) (w0 := w0) r) :
    FibDistLE w0 (RS L (2 ^ (m + ℓ)) : Set (L → F)) δ ∧
      P.g r = resSeq ℓ r (decTable L (m + ℓ) δ w0) := by
  obtain ⟨h1, -⟩ := chain hL hℓ hδ r hgood hπ
  haveI := hL.finite
  have e0 : 2 * Nd m ℓ (0 + 1) = 2 ^ (m + ℓ) := by rw [Nd_succ (by omega)]; rfl
  have hF0 : FibDistLE w0 (RS L (2 ^ (m + ℓ)) : Set (L → F)) δ := by
    have := (h1 0 (by omega)).1
    rw [e0] at this
    exact this
  refine ⟨hF0, ?_⟩
  set fs := decTable L (m + ℓ) δ w0
  have hc0 : chainCw P ℓ w0 δ r 0 = Enc L fs := by
    simp only [chainCw, if_pos (show 0 < ℓ by omega), decAt]
    rw [decTable_spec (show 2 ^ (m + ℓ) ≤ Nat.card L from Nd_le_card hL (j := 0) (by omega)) hF0]
    rw [e0]
    rfl
  have hchain := foldUp_of_chain r (chainCw P ℓ w0 δ r) (fun j hj => (h1 j hj).2) ℓ le_rfl
  rw [hc0, foldUp_Enc hL (by omega) r fs] at hchain
  have hcl : chainCw P ℓ w0 δ r ℓ = ev (lv L ℓ) (ofCoords (P.g r)) := by
    simp only [chainCw, lt_irrefl, if_false]
    exact W_last P w0 hℓ r
  rw [hcl] at hchain
  haveI := lv_finite (L := L) ℓ
  have hd : 2 ^ m ≤ Nat.card (lv L ℓ) := by rw [← Nd_last (ℓ := ℓ)]; exact Nd_le_card hL (by omega)
  have := ev_injOn hd (ofCoords_mem_degreeLT (P.g r)) (ofCoords_mem_degreeLT _) hchain
  rw [← coordsOf_ofCoords (P.g r), this, coordsOf_ofCoords]

end Chain

/-! ### Probability tools -/

section ProbTools

lemma prob_fst {A B : Type*} [Fintype A] [Fintype B] [Nonempty B] (E : A → Prop) :
    prob (fun p : A × B => E p.1) = prob E := by
  classical
  have e : (univ.filter fun p : A × B => E p.1) = (univ.filter E) ×ˢ (univ : Finset B) := by
    ext p; simp
  rw [prob_def, prob_def, e, card_product, Fintype.card_prod]
  have hB : (Fintype.card B : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_pos.ne'
  push_cast
  rw [card_univ, mul_div_mul_right _ _ hB]

lemma card_filter_eq_ncard {α : Type*} [Fintype α] (p : α → Prop) [DecidablePred p] :
    (univ.filter p).card = {a | p a}.ncard := by
  rw [← Set.ncard_coe_finset]; congr 1; ext a; simp

/-- The geometric sum `ε_fold · |F| = ∑_{j=1}^{ℓ} M_j = M (1 - 2^{-ℓ})` (Theorem 7.13), with
`M = 2^μ`, `M_j = 2^{μ-j}`. -/
theorem sum_Mj (μ : ℕ) : ∀ ℓ ≤ μ,
    ∑ j ∈ range ℓ, (2 : ℚ) ^ (μ - (j + 1)) = 2 ^ μ * (1 - 1 / 2 ^ ℓ)
  | 0, _ => by simp
  | ℓ + 1, h => by
      rw [sum_range_succ, sum_Mj μ ℓ (by omega)]
      have e : (2 : ℚ) ^ μ = 2 ^ (μ - (ℓ + 1)) * 2 ^ (ℓ + 1) := by
        rw [← pow_add]; congr 1; omega
      rw [e, pow_succ]
      field_simp
      ring

end ProbTools

/-! ### Theorem 7.13 (soundness) -/

/-- `ε_fold = ∑_{j=1}^{ℓ} M_j / |F|` (Theorem 7.13), with `M_j = 2^{n+R-j}`. -/
noncomputable def epsFold (F : Type*) [Fintype F] (μ ℓ : ℕ) : ℚ :=
  ∑ j ∈ range ℓ, (2 : ℚ) ^ (μ - (j + 1)) / Fintype.card F

/-- `ε_fold = M (1 - 2^{-ℓ}) / |F| < M / |F|` (Theorem 7.13), for `ℓ ≤ μ`, `M = 2^μ`. -/
theorem epsFold_eq (F : Type*) [Fintype F] {μ ℓ : ℕ} (h : ℓ ≤ μ) :
    epsFold F μ ℓ = 2 ^ μ * (1 - 1 / 2 ^ ℓ) / Fintype.card F := by
  rw [epsFold, ← sum_div, sum_Mj μ ℓ h]

theorem epsFold_lt (F : Type*) [Fintype F] [Nonempty F] {μ ℓ : ℕ} (h : ℓ ≤ μ) :
    epsFold F μ ℓ < 2 ^ μ / Fintype.card F := by
  have hF : (0 : ℚ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  rw [epsFold_eq F h]
  apply div_lt_div_of_pos_right _ hF
  have : (0 : ℚ) < 1 / 2 ^ ℓ := by positivity
  have : (0 : ℚ) < 2 ^ μ := by positivity
  nlinarith

section Theorem

variable {L : Subgroup Fˣ} {m : ℕ} (P : EvalProver F L m) (ℓ : ℕ) (w0 : L → F) (zp : ℕ → F)
  (zs : Fin m → F) (v : F) (δ : ℚ)

/-- The honest round polynomials `s*_{j+1}` for the decoded table `f*` of `w₀` (proof of
Theorem 7.13, "Honest values"). -/
noncomputable def sStar (r : ℕ → F) (j : ℕ) : F[X] :=
  honS ℓ r (decTable L (m + ℓ) δ w0) (eqTable (catPt ℓ zp zs)) j

/-- The honest running values `σ*_j` for `f*`. -/
noncomputable def sigStar (r : ℕ → F) (j : ℕ) : F :=
  honSig ℓ r (decTable L (m + ℓ) δ w0) (eqTable (catPt ℓ zp zs)) j

/-- The bad event `E_{j+1}` of the proof of Theorem 7.13, folding part: `r_{j+1}` is not good
for `w_j`. -/
def BadFold (r : ℕ → F) (j : ℕ) : Prop := ¬ GoodAt ℓ δ m j (P.W ℓ w0 r j) (r j)

/-- The bad event `E_{j+1}`, sumcheck part: `s_{j+1} ≠ s*_{j+1}` and
`s_{j+1}(r_{j+1}) = s*_{j+1}(r_{j+1})`. -/
def BadSum (r : ℕ → F) (j : ℕ) : Prop :=
  P.s j r ≠ sStar ℓ w0 zp zs δ r j ∧
    (P.s j r).eval (r j) = (sStar ℓ w0 zp zs δ r j).eval (r j)

variable {P ℓ w0 zp zs v δ}

/-- Proof of Theorem 7.13, "No bad event", case 1. -/
theorem no_bad_far {R : ℕ} (hL : IsSmoothDomain L (m + ℓ + R)) (hℓ : 1 ≤ ℓ)
    (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2)
    (hfar : ¬ FibDistLE w0 (RS L (2 ^ (m + ℓ)) : Set (L → F)) δ) (r : ℕ → F)
    (hgood : ∀ j < ℓ, ¬ BadFold P ℓ w0 δ r j) :
    passFrac (P := P) (ℓ := ℓ) (w0 := w0) r ≤ 1 - δ := by
  by_contra hπ
  push_neg at hπ
  exact hfar (chain_final hL hℓ hδ r (fun j hj => not_not.1 (hgood j hj)) hπ).1

/-- Proof of Theorem 7.13, "No bad event", case 2: if no bad event occurs and the sumcheck and
closure checks pass, then `π(r) ≤ 1 - δ`. -/
theorem no_bad_close {R : ℕ} (hL : IsSmoothDomain L (m + ℓ + R)) (hℓ : 1 ≤ ℓ)
    (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2)
    (hwrong : mle (decTable L (m + ℓ) δ w0) (catPt ℓ zp zs) ≠ v) (r : ℕ → F)
    (hgood : ∀ j < ℓ, ¬ BadFold P ℓ w0 δ r j)
    (hsum : ∀ j < ℓ, ¬ BadSum P ℓ w0 zp zs δ r j)
    (hSC : P.SumcheckOK ℓ v r) (hCl : P.ClosureOK ℓ zp zs v r) :
    passFrac (P := P) (ℓ := ℓ) (w0 := w0) r ≤ 1 - δ := by
  by_contra hπ
  push_neg at hπ
  have hg := (chain_final hL hℓ hδ r (fun j hj => not_not.1 (hgood j hj)) hπ).2
  set fs := decTable L (m + ℓ) δ w0
  -- `v_j ≠ σ*_j` for all `j ≤ ℓ`
  have key : ∀ j ≤ ℓ, P.vv v r j ≠ sigStar ℓ w0 zp zs δ r j := by
    intro j hj
    induction j with
    | zero =>
      simp only [EvalProver.vv, sigStar, honest_sum_zero]
      exact fun h => hwrong h.symm
    | succ j ih =>
      have ih := ih (by omega)
      have hne : P.s j r ≠ sStar ℓ w0 zp zs δ r j := by
        intro heq
        apply ih
        rw [← hSC j (by omega), heq, sStar, sigStar, honS_zero_add_one ℓ r fs _ j (by omega)]
      have hev : (P.s j r).eval (r j) ≠ (sStar ℓ w0 zp zs δ r j).eval (r j) :=
        fun h => hsum j (by omega) ⟨hne, h⟩
      simp only [EvalProver.vv]
      rwa [sStar, honS_eval ℓ r fs _ j (by omega)] at hev
  apply key ℓ le_rfl
  rw [hCl, hg, sigStar, honest_sum_last]

/-- The core of the probability estimate of Theorem 7.13 (proof, "Conclusion"): if acceptance
implies that a bad event `B` occurs or that `π(r) ≤ 1-δ`, then
`Pr[V accepts] ≤ Pr[B] + (1-δ)^κ` (Lemma 3.3 with `𝒜 = {π ≤ 1-δ}` and `𝒮(r) = 𝒫_0`). -/
theorem accProb_le_of [Fintype F] [Fintype L] (κ : ℕ) (B : (ℕ → F) → Prop) (hδ1 : δ ≤ 1)
    (hacc : ∀ r : ℕ → F, P.SumcheckOK ℓ v r → P.ClosureOK ℓ zp zs v r → ¬ B r →
      passFrac (P := P) (ℓ := ℓ) (w0 := w0) r ≤ 1 - δ) :
    evalAccProb P ℓ κ w0 zp zs v ≤
      prob (fun r : Fin ℓ → F => B (extR r)) + (1 - δ) ^ κ := by
  classical
  haveI : Nonempty L := ⟨1⟩
  let S : (Fin ℓ → F) → Finset L := fun ρ =>
    (Set.toFinite (Pass P ℓ w0 (extR ρ) 0)).toFinset
  let A : (Fin ℓ → F) → Prop := fun ρ => passFrac (P := P) (ℓ := ℓ) (w0 := w0) (extR ρ) ≤ 1 - δ
  have hq := (independent_queries_le κ S A (1 - δ) (by linarith) ?_)
  · calc evalAccProb P ℓ κ w0 zp zs v
        ≤ prob (fun ω : (Fin ℓ → F) × (Fin κ → L) =>
            B (extR ω.1) ∨ (A ω.1 ∧ ∀ t, ω.2 t ∈ S ω.1)) := by
          apply prob_mono
          rintro ⟨ρ, ξ⟩ ⟨hSC, hCl, hQ⟩
          by_cases hB : B (extR ρ)
          · exact Or.inl hB
          · refine Or.inr ⟨hacc _ hSC hCl hB, fun t => ?_⟩
            simp only [S, Set.Finite.mem_toFinset]
            exact (mem_Pass_zero _ _).2 (hQ t).1
      _ ≤ prob (fun ω : (Fin ℓ → F) × (Fin κ → L) => B (extR ω.1)) +
            prob (fun ω : (Fin ℓ → F) × (Fin κ → L) => A ω.1 ∧ ∀ t, ω.2 t ∈ S ω.1) :=
          prob_or_le _ _
      _ ≤ _ := by
          rw [prob_fst (fun ρ : Fin ℓ → F => B (extR ρ))]
          exact add_le_add_left (hq.1.trans hq.2) _
  · intro ρ hA
    simp only [S]
    rw [← Set.ncard_eq_toFinset_card, ← Nat.card_eq_fintype_card]
    have hpos : (0 : ℚ) < Nat.card L := by exact_mod_cast Nat.card_pos
    simp only [A, passFrac] at hA
    rwa [div_le_iff₀ hpos] at hA

/-- Per-round count for the folding part of the bad events (Lemma 7.9 at level `j+1`). -/
theorem card_badFold_le [Fintype F] [DecidableEq F] {R : ℕ} (hL : IsSmoothDomain L (m + ℓ + R))
    (hδ0 : 0 < δ) (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2) {j : ℕ} (hj : j < ℓ) (w : lv L j → F) :
    {c : F | ¬ GoodAt ℓ δ m j w c}.ncard ≤ Nat.card (lv L (j + 1)) := by
  obtain ⟨hDj, hμj, hdD, hrate⟩ := level_facts hL hj
  have hδj : δ ≤ (1 - rate (sqDom (lv L j)) (Nd m ℓ (j + 1))) / 2 := by rw [hrate]; exact hδ
  exact ncard_not_good_le hDj hμj (Nd_pos _ _ _) hdD hδ0 hδj w

/-- **Theorem 7.13(1) (soundness, far commitment).** Let `1 ≤ ℓ`, `L` a smooth domain of order
`M = 2^{n+R}` (`n = m + ℓ`), `0 < δ ≤ (1-ρ)/2` with `ρ = 2^{-R}`, and let the prover be causal.
If `Δ^fib₀(w₀, 𝒞₀) > δ`, the verifier accepts with probability at most
`ε_fold + (1-δ)^κ`, `ε_fold = ∑_{j=1}^{ℓ} M_j/|F|`. -/
theorem soundness_far [Fintype F] [DecidableEq F] [Fintype L] {R : ℕ}
    (hL : IsSmoothDomain L (m + ℓ + R)) (hℓ : 1 ≤ ℓ) (hδ0 : 0 < δ)
    (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2) (hC : P.Causal) (κ : ℕ)
    (hfar : ¬ FibDistLE w0 (RS L (2 ^ (m + ℓ)) : Set (L → F)) δ) :
    evalAccProb P ℓ κ w0 zp zs v ≤ epsFold F (m + ℓ + R) ℓ + (1 - δ) ^ κ := by
  classical
  have hR : (0 : ℚ) < 1 / 2 ^ R := by positivity
  refine (accProb_le_of κ (fun r => ∃ j < ℓ, BadFold P ℓ w0 δ r j) (by linarith)
    (fun r _ _ hB => no_bad_far hL hℓ hδ hfar r (fun j hj h => hB ⟨j, hj, h⟩))).trans ?_
  apply add_le_add_right
  -- Lemma 3.2 with `k_j = M_{j+1}`
  let E : Fin ℓ → (Fin ℓ → F) → Prop := fun i ρ => BadFold P ℓ w0 δ (extR ρ) i
  have hseq := sequential_challenges (Ch := fun _ : Fin ℓ => F) E
    (fun i => (Nat.card (lv L ((i : ℕ) + 1)) : ℚ)) ?_
  · calc prob (fun ρ : Fin ℓ → F => ∃ j < ℓ, BadFold P ℓ w0 δ (extR ρ) j)
        ≤ prob (fun ρ : Fin ℓ → F => ∃ i, E i ρ) := by
          apply prob_mono
          rintro ρ ⟨j, hj, h⟩
          exact ⟨⟨j, hj⟩, h⟩
      _ ≤ _ := hseq
      _ = epsFold F (m + ℓ + R) ℓ := by
          rw [epsFold, ← Fin.sum_univ_eq_sum_range]
          refine sum_congr rfl (fun i _ => ?_)
          rw [card_lv hL (by omega)]; push_cast; rfl
  · intro i ρ
    have hE : ∀ c : F, E i (Function.update ρ i c) ↔
        ¬ GoodAt ℓ δ m i (P.W ℓ w0 (extR ρ) i) c := by
      intro c
      simp only [E, BadFold, extR_update]
      rw [W_congr P w0 hC i.isLt (fun k hk => Function.update_of_ne (by omega) _ _),
        Function.update_self]
    simp_rw [hE]
    rw [card_filter_eq_ncard]
    exact_mod_cast card_badFold_le hL hδ0 hδ i.isLt _

/-- **Theorem 7.13(2) (soundness, wrong value).** Under the hypotheses of `soundness_far`, and
with round polynomials of degree `≤ 2`: if the decoded table `f*` of `w₀` satisfies
`f*~(z) ≠ v`, the verifier accepts with probability at most `ε_fold + 2ℓ/|F| + (1-δ)^κ`.
(The paper also assumes `Δ^fib₀(w₀, 𝒞₀) ≤ δ`; the bound holds without it.) -/
theorem soundness_close [Fintype F] [DecidableEq F] [Fintype L] {R : ℕ}
    (hL : IsSmoothDomain L (m + ℓ + R)) (hℓ : 1 ≤ ℓ) (hδ0 : 0 < δ)
    (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2) (hC : P.Causal) (hdeg : P.DegOK) (κ : ℕ)
    (hwrong : mle (decTable L (m + ℓ) δ w0) (catPt ℓ zp zs) ≠ v) :
    evalAccProb P ℓ κ w0 zp zs v ≤
      epsFold F (m + ℓ + R) ℓ + 2 * ℓ / Fintype.card F + (1 - δ) ^ κ := by
  classical
  have hR : (0 : ℚ) < 1 / 2 ^ R := by positivity
  refine (accProb_le_of κ (fun r => ∃ j < ℓ, BadFold P ℓ w0 δ r j ∨ BadSum P ℓ w0 zp zs δ r j)
    (by linarith) (fun r hSC hCl hB => no_bad_close hL hℓ hδ hwrong r
      (fun j hj h => hB ⟨j, hj, Or.inl h⟩) (fun j hj h => hB ⟨j, hj, Or.inr h⟩) hSC hCl)).trans ?_
  apply add_le_add_right
  let E : Fin ℓ → (Fin ℓ → F) → Prop := fun i ρ =>
    BadFold P ℓ w0 δ (extR ρ) i ∨ BadSum P ℓ w0 zp zs δ (extR ρ) i
  have hseq := sequential_challenges (Ch := fun _ : Fin ℓ => F) E
    (fun i => (Nat.card (lv L ((i : ℕ) + 1)) : ℚ) + 2) ?_
  · calc prob (fun ρ : Fin ℓ → F =>
          ∃ j < ℓ, BadFold P ℓ w0 δ (extR ρ) j ∨ BadSum P ℓ w0 zp zs δ (extR ρ) j)
        ≤ prob (fun ρ : Fin ℓ → F => ∃ i, E i ρ) := by
          apply prob_mono
          rintro ρ ⟨j, hj, h⟩
          exact ⟨⟨j, hj⟩, h⟩
      _ ≤ _ := hseq
      _ = epsFold F (m + ℓ + R) ℓ + 2 * ℓ / Fintype.card F := by
          rw [epsFold, ← Fin.sum_univ_eq_sum_range]
          simp only [add_div, sum_add_distrib]
          congr 1
          · refine sum_congr rfl (fun i _ => ?_)
            rw [card_lv hL (by omega)]; push_cast; rfl
          · simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  · intro i ρ
    set r := extR ρ
    have hupd : ∀ c : F, ∀ k < (i : ℕ), Function.update r i c k = r k :=
      fun c k hk => Function.update_of_ne (by omega) _ _
    have hE : ∀ c : F, E i (Function.update ρ i c) ↔
        (¬ GoodAt ℓ δ m i (P.W ℓ w0 r i) c ∨
          (P.s i r ≠ sStar ℓ w0 zp zs δ r i ∧
            (P.s i r).eval c = (sStar ℓ w0 zp zs δ r i).eval c)) := by
      intro c
      simp only [E, BadFold, BadSum, extR_update, sStar]
      rw [W_congr P w0 hC i.isLt (hupd c), hC.1 i _ r (hupd c),
        honS_congr ℓ _ r _ _ i (hupd c), Function.update_self]
    simp_rw [hE]
    rw [filter_or]
    refine (Nat.cast_le.2 (card_union_le _ _)).trans ?_
    push_cast
    apply add_le_add
    · rw [card_filter_eq_ncard]
      exact_mod_cast card_badFold_le hL hδ0 hδ i.isLt _
    · by_cases hne : P.s i r ≠ sStar ℓ w0 zp zs δ r i
      · simp only [hne, ne_eq, not_false_eq_true, true_and]
        exact_mod_cast card_agree_le_two _ _ hne (hdeg i r) (natDegree_honS ℓ r _ _ i)
      · simp [hne]

/-- **Corollary 7.14 (evaluation binding).** Let `1 ≤ ℓ` and
`ε = ε_fold + 2ℓ/|F| + (1-δ)^κ`.  If some causal prover with round polynomials of degree `≤ 2`
makes the verifier accept `(w₀; z, v)` with probability greater than `ε`, then
`Δ^fib₀(w₀, 𝒞₀) ≤ δ` and `v = f*~(z)` for the decoded table `f*` of `w₀`.
(Randomised provers reduce to deterministic ones by Lemma 3.4, `avg_le_of_forall_le`.) -/
theorem eval_binding [Fintype F] [DecidableEq F] [Fintype L] {R : ℕ}
    (hL : IsSmoothDomain L (m + ℓ + R)) (hℓ : 1 ≤ ℓ) (hδ0 : 0 < δ)
    (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2) (hC : P.Causal) (hdeg : P.DegOK) (κ : ℕ)
    (hacc : epsFold F (m + ℓ + R) ℓ + 2 * ℓ / Fintype.card F + (1 - δ) ^ κ
      < evalAccProb P ℓ κ w0 zp zs v) :
    FibDistLE w0 (RS L (2 ^ (m + ℓ)) : Set (L → F)) δ ∧
      v = mle (decTable L (m + ℓ) δ w0) (catPt ℓ zp zs) := by
  have hF : (0 : ℚ) ≤ 2 * ℓ / Fintype.card F := by positivity
  constructor
  · by_contra hfar
    have := soundness_far (v := v) (zp := zp) (zs := zs) hL hℓ hδ0 hδ hC κ hfar
    linarith
  · by_contra hne
    have := soundness_close hL hℓ hδ0 hδ hC hdeg κ (fun h => hne h.symm)
    linarith

/-- **Corollary 7.14, "in particular":** `Π_eval` is `ε`-evaluation binding (Definition 3.11): for
a fixed commitment `w₀` and point `z`, no two distinct values `v ≠ v'` can both be accepted with
probability `> ε` by (causal, degree-`≤ 2`) deterministic provers. -/
theorem eval_binding' [Fintype F] [DecidableEq F] [Fintype L] {R : ℕ}
    (hL : IsSmoothDomain L (m + ℓ + R)) (hℓ : 1 ≤ ℓ) (hδ0 : 0 < δ)
    (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2) (κ : ℕ) {v' : F} (hvv : v ≠ v')
    (P' : EvalProver F L m) (hC : P.Causal) (hdeg : P.DegOK) (hC' : P'.Causal)
    (hdeg' : P'.DegOK) :
    ¬ (epsFold F (m + ℓ + R) ℓ + 2 * ℓ / Fintype.card F + (1 - δ) ^ κ
          < evalAccProb P ℓ κ w0 zp zs v ∧
        epsFold F (m + ℓ + R) ℓ + 2 * ℓ / Fintype.card F + (1 - δ) ^ κ
          < evalAccProb P' ℓ κ w0 zp zs v') := by
  rintro ⟨h1, h2⟩
  have e1 := (eval_binding hL hℓ hδ0 hδ hC hdeg κ h1).2
  have e2 := (eval_binding hL hℓ hδ0 hδ hC' hdeg' κ h2).2
  exact hvv (e1.trans e2.symm)

end Theorem

/-! ### Proposition 7.15 (the case `ℓ = 0`) -/

section NoFolding

variable {L : Subgroup Fˣ} {m : ℕ}

/-- For `ℓ = 0` the challenge vector is empty. -/
lemma extR_zero (ρ : Fin 0 → F) : extR ρ = fun _ => 0 := by
  funext i; simp [extR]

/-- For `ℓ = 0`, the verifier accepts iff `v = g~(z)` and every query point lies in
`S = {ξ ∈ L : w₀(ξ) = G(ξ)}`. -/
lemma accepts_zero (P : EvalProver F L m) (w0 : L → F) (zp : ℕ → F) (zs : Fin m → F) (v : F)
    {κ : ℕ} (r : ℕ → F) (ξ : Fin κ → L) :
    P.Accepts 0 w0 zp zs v r ξ ↔
      v = mle (P.g r) zs ∧ ∀ t, w0 (ξ t) = (ofCoords (P.g r)).eval (((ξ t : L) : Fˣ) : F) := by
  simp [EvalProver.Accepts, EvalProver.SumcheckOK, EvalProver.ClosureOK, EvalProver.QueryOK,
    EvalProver.vv]

/-- **Proposition 7.15 (no folding).** Let `ℓ = 0`, `L` a smooth domain of order `2^{n+R}`
(`n = m`), `δ ≤ (1-ρ)/2`.  If a deterministic prover makes the verifier accept `(w₀; z, v)` with
probability greater than `(1-δ)^κ`, then its (fixed) final table `g` satisfies
`Δ(w₀, Enc(g)) < δ` (so `Δ(w₀, 𝒞₀) < δ`), `v = g~(z)`, and `g = f^H` is the unique table with
`Δ(w₀, Enc(f^H)) ≤ δ`. -/
theorem no_folding [Fintype F] [DecidableEq F] [Fintype L] {R : ℕ}
    (hL : IsSmoothDomain L (m + R)) {δ : ℚ} (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2) (κ : ℕ)
    (P : EvalProver F L m) (w0 : L → F) (zp : ℕ → F) (zs : Fin m → F) (v : F)
    (hacc : (1 - δ) ^ κ < evalAccProb P 0 κ w0 zp zs v) :
    relDist w0 (Enc L (P.g fun _ => 0)) < δ ∧ v = mle (P.g fun _ => 0) zs ∧
      ∀ f : Table F m, relDist w0 (Enc L f) ≤ δ → f = P.g fun _ => 0 := by
  classical
  haveI : Nonempty L := ⟨1⟩
  set g0 := P.g fun _ => 0
  have hR : (0 : ℚ) < 1 / 2 ^ R := by positivity
  let S : Finset L := univ.filter (fun ξ => w0 ξ = (ofCoords g0).eval (((ξ : L) : Fˣ) : F))
  let A : Prop := v = mle g0 zs
  have hev : (fun ω : (Fin 0 → F) × (Fin κ → L) => P.Accepts 0 w0 zp zs v (extR ω.1) ω.2) =
      fun ω => (fun _ : Fin 0 → F => A) ω.1 ∧ ∀ t, ω.2 t ∈ (fun _ : Fin 0 → F => S) ω.1 := by
    funext ω
    rw [accepts_zero, extR_zero]
    simp [S, A, g0]
  have hq := independent_queries (Ω' := Fin 0 → F) κ (fun _ => S) (fun _ => A)
  rw [evalAccProb, hev, hq] at hacc
  simp only [expect, Fintype.univ_ofSubsingleton, sum_singleton, Fintype.card_unique,
    Nat.cast_one, div_one] at hacc
  by_cases hA : A
  · rw [if_pos hA] at hacc
    have hM : (0 : ℚ) < Fintype.card L := by exact_mod_cast Fintype.card_pos
    -- `|S|/M > 1 - δ`
    have hSM : 1 - δ < (S.card : ℚ) / Fintype.card L := by
      by_contra hle
      push_neg at hle
      have h1 : (0 : ℚ) ≤ 1 - δ := by linarith
      have := pow_le_pow_left₀ (by positivity) hle κ
      linarith
    have hagree : agreeSet w0 (Enc L g0) = (S : Set L) := by
      ext ξ; simp [agreeSet, S, Enc, ev]
    have hdist : relDist w0 (Enc L g0) < δ := by
      have h := agree_add_hdist w0 (Enc L g0)
      rw [hagree, Set.ncard_coe_finset] at h
      have h' : (S.card : ℚ) + hdist w0 (Enc L g0) = Nat.card L := by exact_mod_cast h
      rw [Nat.card_eq_fintype_card] at h'
      unfold relDist
      rw [Nat.card_eq_fintype_card, div_lt_iff₀ hM]
      rw [lt_div_iff₀ hM] at hSM
      linarith
    refine ⟨hdist, hA, fun f hf => ?_⟩
    have hrate : rate L (2 ^ m) = 1 / 2 ^ R := rate_lv (ℓ := 0) hL (j := 0) (by omega)
    have hδ' : δ ≤ (1 - rate L (2 ^ m)) / 2 := by rw [hrate]; exact hδ
    haveI := hL.finite
    have := RS_unique_decoding' δ hδ' w0 (Enc_mem_RS L f) (Enc_mem_RS L g0) hf hdist.le
    exact Enc_injective (show 2 ^ m ≤ Nat.card L from Nd_le_card (ℓ := 0) hL (j := 0) (by omega))
      this
  · rw [if_neg hA] at hacc
    have : (0 : ℚ) ≤ (1 - δ) ^ κ := pow_nonneg (by linarith) κ
    linarith

end NoFolding

end KBFold
