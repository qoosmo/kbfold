/-
SumFRI/Soundness.lean
§6.4–6.5 of the Sum-FRI paper: passing sets (Lemma 6.11), the codeword chain (Lemma 6.12), the
soundness theorem (Theorem 6.13), evaluation binding (Corollary 6.14), the sum protocol
(Corollary 6.15) and the case `ℓ = 0` (Proposition 6.16).

Setting (see `SumFRI/Scheme.lean` for the modelling of `Π_eval`).
* `n = m + ℓ` variables, `1 ≤ ℓ`; `L` is a smooth domain of order `M = 2^{n+R}`; the levels
  `L_j = lv L j`, the degree bounds `N_j = Nd m ℓ j` and the facts `rate_lv`, `level_facts`,
  `Nd_succ`, `Nd_le_card`, `card_lv` are those of `KBFold/Soundness.lean`.
* `0 < δ ≤ (1-ρ)/2`, `ρ = 2^{-R}`.
* A fixed deterministic prover `P : SumProver F L m`, causal and with affine round polynomials,
  and an instance `(w₀; z, v)` with `z = catPt ℓ zp zs`.
The probability tools (`sequential_challenges`, `independent_queries_le`, `prob_fst`,
`card_filter_eq_ncard`) and `ε_fold` (`epsFold`, `epsFold_eq`) are those of KBFold.
Names are prefixed with `c` where KBFold has a declaration with the same role.
-/
import SumFRI.Fibre
import KBFold.Soundness

set_option autoImplicit false

open Polynomial Finset

namespace SumFRI

open KBFold

variable {F : Type*} [Field F]

/-! ### Passing sets (Lemma 6.11) -/

section Passing

variable {L : Subgroup Fˣ} {m : ℕ} (P : SumProver F L m) (ℓ : ℕ) (w0 : L → F)

/-- **Passing sets** (§6.4): `𝒫_j ⊆ L_j` is the set of points `ξ_j = ξ₀^{2^j}` for which the
query checks at levels `j+1, …, ℓ` pass. -/
def cPass (θ : ℕ → F) (j : ℕ) : Set (lv L j) :=
  {η | ∃ ξ : L, ptAt ξ j = η ∧ ∀ i, j ≤ i → i < ℓ → P.Chk ℓ w0 θ i (ptAt ξ (i + 1))}

variable {P ℓ w0}

/-- **Lemma 6.11(1).** -/
theorem cptAt_mem_Pass (θ : ℕ → F) (j : ℕ) (ξ : L) :
    ptAt ξ j ∈ cPass P ℓ w0 θ j ↔ ∀ i, j ≤ i → i < ℓ → P.Chk ℓ w0 θ i (ptAt ξ (i + 1)) := by
  constructor
  · rintro ⟨ξ', he, h⟩ i hji hi
    rw [← ptAt_congr he (i + 1) (by omega)]
    exact h i hji hi
  · intro h; exact ⟨ξ, rfl, h⟩

/-- **Lemma 6.11(1), `j = 0`:** `ξ₀` passes all the query checks iff `ξ₀ ∈ 𝒫_0`. -/
theorem cmem_Pass_zero (θ : ℕ → F) (ξ : L) :
    ξ ∈ cPass P ℓ w0 θ 0 ↔ ∀ i < ℓ, P.Chk ℓ w0 θ i (ptAt ξ (i + 1)) := by
  have := cptAt_mem_Pass (P := P) (ℓ := ℓ) (w0 := w0) θ 0 ξ
  simp only [zero_le, true_implies] at this
  exact this

/-- The recursive description of the passing sets. -/
theorem cmem_Pass_iff (θ : ℕ → F) {j : ℕ} (hj : j < ℓ) (η : lv L j) :
    η ∈ cPass P ℓ w0 θ j ↔ sqPt η ∈ cPass P ℓ w0 θ (j + 1) ∧ P.Chk ℓ w0 θ j (sqPt η) := by
  obtain ⟨ξ, rfl⟩ := ptAt_surjective j η
  have e : sqPt (ptAt ξ j) = ptAt ξ (j + 1) := rfl
  rw [e, cptAt_mem_Pass, cptAt_mem_Pass]
  constructor
  · intro h
    exact ⟨fun i hi hiℓ => h i (by omega) hiℓ, h j le_rfl hj⟩
  · rintro ⟨h1, h2⟩ i hi hiℓ
    rcases Nat.eq_or_lt_of_le hi with rfl | hlt
    · exact h2
    · exact h1 i hlt hiℓ

/-- **Lemma 6.11(2):** for `j < ℓ`, `𝒫_j` is a union of fibres ... -/
theorem cPass_neg (θ : ℕ → F) {j : ℕ} (hj : j < ℓ)
    (η : lv L j) (hη : η ∈ cPass P ℓ w0 θ j) : negPt η ∈ cPass P ℓ w0 θ j := by
  rw [cmem_Pass_iff θ hj] at hη ⊢
  rwa [sqPt_negPt]

/-- **Lemma 6.11(2):** ... and squaring maps it into `𝒫_{j+1}`. -/
theorem csq_Pass_subset (θ : ℕ → F) {j : ℕ} (hj : j < ℓ) :
    sqPt '' cPass P ℓ w0 θ j ⊆ cPass P ℓ w0 θ (j + 1) := by
  rintro _ ⟨η, hη, rfl⟩
  exact ((cmem_Pass_iff θ hj η).1 hη).1

/-- The fraction `π(θ) = |𝒫_0| / M` of passing query points. -/
noncomputable def cpassFrac (θ : ℕ → F) : ℚ := ((cPass P ℓ w0 θ 0).ncard : ℚ) / Nat.card L

/-- **Lemma 6.11(2)–(3)**, halving step. -/
theorem cPass_card_step {R : ℕ} (hL : IsSmoothDomain L (m + ℓ + R)) (θ : ℕ → F) (j : ℕ)
    (hj : j < ℓ) (h : cpassFrac (P := P) (ℓ := ℓ) (w0 := w0) θ * Nat.card (lv L j)
        ≤ (cPass P ℓ w0 θ j).ncard) :
    cpassFrac (P := P) (ℓ := ℓ) (w0 := w0) θ * Nat.card (lv L (j + 1))
      ≤ (sqPt '' cPass P ℓ w0 θ j).ncard := by
  haveI := hL.finite
  haveI := lv_finite (L := L) j
  have hneg := lv_neg_one_mem hL (j := j) (by omega)
  have h2F := two_ne_zero_of_smooth hL (by omega : 1 ≤ m + ℓ + R)
  have hc := ncard_eq_two_mul_image hneg h2F (cPass P ℓ w0 θ j)
    (fun η hη => cPass_neg θ hj η hη)
  have hM := card_lv_succ hL (j := j) (by omega)
  rw [hc, hM] at h
  push_cast at h
  linarith

/-- **Lemma 6.11(3):** `|𝒫_j| ≥ π M_j` for every `j ≤ ℓ`. -/
theorem cPass_card {R : ℕ} (hL : IsSmoothDomain L (m + ℓ + R)) (θ : ℕ → F) :
    ∀ j ≤ ℓ, cpassFrac (P := P) (ℓ := ℓ) (w0 := w0) θ * Nat.card (lv L j)
        ≤ (cPass P ℓ w0 θ j).ncard
  | 0, _ => by
      haveI := hL.finite
      have hpos : (0 : ℚ) < Nat.card L := by
        haveI : Nonempty L := ⟨1⟩; exact_mod_cast Nat.card_pos
      have e : Nat.card (lv L 0) = Nat.card L := rfl
      rw [e, cpassFrac, div_mul_cancel₀ _ hpos.ne']
  | j + 1, hj => by
      haveI := hL.finite
      haveI := lv_finite (L := L) (j + 1)
      refine (cPass_card_step hL θ j (by omega) (cPass_card hL θ j (by omega))).trans ?_
      have := Set.ncard_le_ncard (csq_Pass_subset (P := P) (w0 := w0) θ (j := j) (by omega))
        (Set.toFinite (cPass P ℓ w0 θ (j + 1)))
      exact_mod_cast this

/-- **Lemma 6.11(2)–(3):** `|𝒫_j²| ≥ π M_{j+1}` for `j < ℓ`. -/
theorem csq_Pass_card {R : ℕ} (hL : IsSmoothDomain L (m + ℓ + R)) (θ : ℕ → F) {j : ℕ}
    (hj : j < ℓ) : cpassFrac (P := P) (ℓ := ℓ) (w0 := w0) θ * Nat.card (lv L (j + 1))
      ≤ (sqPt '' cPass P ℓ w0 θ j).ncard :=
  cPass_card_step hL θ j hj (cPass_card hL θ j hj.le)

end Passing

/-! ### The oracle words -/

section Words

variable {L : Subgroup Fˣ} {m : ℕ} (P : SumProver F L m) {ℓ : ℕ} (w0 : L → F)

/-- The last word `w_ℓ = ev_{L_ℓ}(V_g)`. -/
lemma cW_last (hℓ : 1 ≤ ℓ) (θ : ℕ → F) : P.W ℓ w0 θ ℓ = ev (lv L ℓ) (vpoly (P.g θ)) := by
  obtain ⟨k, rfl⟩ : ∃ k, ℓ = k + 1 := ⟨ℓ - 1, by omega⟩
  simp [SumProver.W]

lemma cW_mid {j : ℕ} (hj0 : 0 < j) (hj : j < ℓ) (θ : ℕ → F) : P.W ℓ w0 θ j = P.orc j θ := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  simp only [SumProver.W]
  rw [if_neg (by omega)]

/-- The words `w_j`, `j < ℓ`, depend only on `θ_{<j}` (causality). -/
lemma cW_congr (hC : P.Causal) {j : ℕ} (hj : j < ℓ) {θ θ' : ℕ → F}
    (h : ∀ k < j, θ k = θ' k) : P.W ℓ w0 θ j = P.W ℓ w0 θ' j := by
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · rfl
  · rw [cW_mid P w0 hj0 hj, cW_mid P w0 hj0 hj, hC.2 j θ θ' h]

lemma cW_last_mem_RS (hℓ : 1 ≤ ℓ) (θ : ℕ → F) : P.W ℓ w0 θ ℓ ∈ RS (lv L ℓ) (Nd m ℓ ℓ) := by
  rw [cW_last P w0 hℓ, Nd_last]; exact ev_mem_RS (vpoly_mem_degreeLT _)

end Words

/-- A sequence of words `c_j` on the levels with `cfold_{θ_{j+1}}(c_j) = c_{j+1}` is the
sequence of successive classical folds of `c_0`. -/
lemma cfoldUp_of_chain {L : Subgroup Fˣ} {ℓ : ℕ} (θ : ℕ → F) (c : (j : ℕ) → lv L j → F)
    (h : ∀ j < ℓ, cwfold (θ j) (c j) = c (j + 1)) : ∀ j ≤ ℓ, c j = cfoldUp θ (c 0) j
  | 0, _ => rfl
  | j + 1, hj => by
      rw [cfoldUp, ← cfoldUp_of_chain θ c h j (by omega), h j (by omega)]

/-! ### Lemma 6.12 (the codeword chain) -/

section Chain

variable {L : Subgroup Fˣ} {m : ℕ} (P : SumProver F L m) (ℓ : ℕ) (w0 : L → F) (δ : ℚ)

/-- **Definition 6.8 at level `j+1`:** `θ` is good for `w ∈ F^{L_j}`. -/
def cGoodAt (m : ℕ) (j : ℕ) (w : lv L j → F) (θ : F) : Prop := CGood δ (Nd m ℓ (j + 1)) w θ

/-- **Definition 6.4 at level `j`:** `dec_j(w)`, for `w ∈ F^{L_j}`, `j < ℓ`. -/
noncomputable def cdecAt (m : ℕ) (j : ℕ) (w : lv L j → F) : lv L j → F :=
  dec (RS (lv L j) (2 * Nd m ℓ (j + 1)) : Set (lv L j → F)) δ w

/-- The codeword chain of Lemma 6.12: `c_j = dec_j(w_j)` for `j < ℓ` and `c_ℓ = w_ℓ`. -/
noncomputable def cchainCw (θ : ℕ → F) (j : ℕ) : lv L j → F :=
  if j < ℓ then cdecAt ℓ δ m j (P.W ℓ w0 θ j) else P.W ℓ w0 θ j

variable {P ℓ w0 δ}

/-- **Lemma 6.12 (the codeword chain).** Fix `θ` such that `θ_{j+1}` is good for `w_j` for every
`j < ℓ`, and `π(θ) > 1-δ`.  Then `Δ^fib_j(w_j, 𝒞_j) ≤ δ` for every `j < ℓ`, and the codewords
`c_j = dec_j(w_j)` (`j < ℓ`), `c_ℓ = w_ℓ` satisfy `cfold_{θ_{j+1}}(c_j) = c_{j+1}` and
`w_j = c_j` on `𝒫_j`. -/
theorem cchain {R : ℕ} (hL : IsSmoothDomain L (m + ℓ + R)) (hℓ : 1 ≤ ℓ)
    (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2) (θ : ℕ → F)
    (hgood : ∀ j < ℓ, cGoodAt ℓ δ m j (P.W ℓ w0 θ j) (θ j))
    (hπ : 1 - δ < cpassFrac (P := P) (ℓ := ℓ) (w0 := w0) θ) :
    (∀ j < ℓ, FibDistLE (P.W ℓ w0 θ j) (RS (lv L j) (2 * Nd m ℓ (j + 1)) : Set _) δ ∧
        cwfold (θ j) (cchainCw P ℓ w0 δ θ j) = cchainCw P ℓ w0 δ θ (j + 1)) ∧
      ∀ j ≤ ℓ, ∀ η ∈ cPass P ℓ w0 θ j, P.W ℓ w0 θ j η = cchainCw P ℓ w0 δ θ j η := by
  let Q : ℕ → Prop := fun j =>
    (j < ℓ → FibDistLE (P.W ℓ w0 θ j) (RS (lv L j) (2 * Nd m ℓ (j + 1)) : Set _) δ ∧
        cwfold (θ j) (cchainCw P ℓ w0 δ θ j) = cchainCw P ℓ w0 δ θ (j + 1)) ∧
      ∀ η ∈ cPass P ℓ w0 θ j, P.W ℓ w0 θ j η = cchainCw P ℓ w0 δ θ j η
  have key : ∀ k j, j + k = ℓ → Q j := by
    intro k
    induction k with
    | zero =>
      intro j hj
      simp only [add_zero] at hj
      subst hj
      refine ⟨fun h => absurd h (lt_irrefl _), fun η _ => ?_⟩
      simp [cchainCw]
    | succ k ih =>
      intro j hjk
      have hj : j < ℓ := by omega
      obtain ⟨ihF, ihP⟩ := ih (j + 1) (by omega)
      obtain ⟨hDj, hμj, hdD, hrate⟩ := level_facts hL hj
      have hδj : δ ≤ (1 - rate (sqDom (lv L j)) (Nd m ℓ (j + 1))) / 2 := by rw [hrate]; exact hδ
      haveI := hL.finite
      haveI : Finite (sqDom (lv L j)) := lv_finite (L := L) (j + 1)
      have hc' : cchainCw P ℓ w0 δ θ (j + 1) ∈ RS (sqDom (lv L j)) (Nd m ℓ (j + 1)) := by
        by_cases hj1 : j + 1 < ℓ
        · have hF := (ihF hj1).1
          have hmem := (dec_spec hF).1
          simp only [cchainCw, if_pos hj1, cdecAt]
          have e : 2 * Nd m ℓ (j + 1 + 1) = Nd m ℓ (j + 1) := Nd_succ (by omega)
          rw [e] at hmem ⊢
          exact hmem
        · have e : j + 1 = ℓ := by omega
          simp only [cchainCw, if_neg hj1]
          have := cW_last_mem_RS P w0 hℓ θ
          subst e
          exact this
      have hsub : sqPt '' cPass P ℓ w0 θ j ⊆
          agreeSet (cwfold (θ j) (P.W ℓ w0 θ j)) (cchainCw P ℓ w0 δ θ (j + 1)) := by
        rintro _ ⟨η, hη, rfl⟩
        obtain ⟨h1, h2⟩ := (cmem_Pass_iff θ hj η).1 hη
        show cwfold (θ j) (P.W ℓ w0 θ j) (sqPt η) = cchainCw P ℓ w0 δ θ (j + 1) (sqPt η)
        rw [← ihP _ h1]
        exact h2
      have hY : (1 - δ) * Nat.card (sqDom (lv L j)) ≤
          (agreeSet (cwfold (θ j) (P.W ℓ w0 θ j)) (cchainCw P ℓ w0 δ θ (j + 1))).ncard := by
        have h1 := csq_Pass_card (P := P) (w0 := w0) hL θ hj
        have h2 : ((sqPt '' cPass P ℓ w0 θ j).ncard : ℚ) ≤
            (agreeSet (cwfold (θ j) (P.W ℓ w0 θ j)) (cchainCw P ℓ w0 δ θ (j + 1))).ncard := by
          exact_mod_cast Set.ncard_le_ncard hsub (Set.toFinite _)
        have h3 : (0 : ℚ) ≤ Nat.card (lv L (j + 1)) := Nat.cast_nonneg _
        have h4 : (1 - δ) * Nat.card (lv L (j + 1)) ≤
            cpassFrac (P := P) (ℓ := ℓ) (w0 := w0) θ * Nat.card (lv L (j + 1)) :=
          mul_le_mul_of_nonneg_right hπ.le h3
        exact h4.trans (h1.trans h2)
      obtain ⟨hF, hfold, hagree⟩ :=
        cone_step hDj hμj hδj (P.W ℓ w0 θ j) (θ j) (hgood j hj) _ hc' hY
      have hcj : cchainCw P ℓ w0 δ θ j = dec (RS (lv L j) (2 * Nd m ℓ (j + 1)) : Set _) δ
          (P.W ℓ w0 θ j) := by
        simp only [cchainCw, if_pos hj, cdecAt]
      refine ⟨fun _ => ⟨hF, by rw [hcj]; exact hfold⟩, fun η hη => ?_⟩
      rw [hcj]
      exact hagree (sqPt η) (hsub ⟨η, hη, rfl⟩) η rfl
  refine ⟨fun j hj => (key (ℓ - j) j (by omega)).1 hj, fun j hj => (key (ℓ - j) j (by omega)).2⟩

/-- **Lemma 6.12, last claim:** under the hypotheses of `cchain`, `Δ^fib₀(w₀, 𝒞₀) ≤ δ` and the
final table is `g = cres_θ(f*)`, where `f*` is the decoded table of `w₀`. -/
theorem cchain_final {R : ℕ} (hL : IsSmoothDomain L (m + ℓ + R)) (hℓ : 1 ≤ ℓ)
    (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2) (θ : ℕ → F)
    (hgood : ∀ j < ℓ, cGoodAt ℓ δ m j (P.W ℓ w0 θ j) (θ j))
    (hπ : 1 - δ < cpassFrac (P := P) (ℓ := ℓ) (w0 := w0) θ) :
    FibDistLE w0 (RS L (2 ^ (m + ℓ)) : Set (L → F)) δ ∧
      P.g θ = cresSeq ℓ θ (cdecTable L (m + ℓ) δ w0) := by
  obtain ⟨h1, -⟩ := cchain hL hℓ hδ θ hgood hπ
  haveI := hL.finite
  have e0 : 2 * Nd m ℓ (0 + 1) = 2 ^ (m + ℓ) := by rw [Nd_succ (by omega)]; rfl
  have hF0 : FibDistLE w0 (RS L (2 ^ (m + ℓ)) : Set (L → F)) δ := by
    have := (h1 0 (by omega)).1
    rw [e0] at this
    exact this
  refine ⟨hF0, ?_⟩
  set fs := cdecTable L (m + ℓ) δ w0
  have hc0 : cchainCw P ℓ w0 δ θ 0 = cEnc L fs := by
    simp only [cchainCw, if_pos (show 0 < ℓ by omega), cdecAt]
    rw [cdecTable_spec (show 2 ^ (m + ℓ) ≤ Nat.card L from Nd_le_card hL (j := 0) (by omega)) hF0]
    rw [e0]
    rfl
  have hchain := cfoldUp_of_chain θ (cchainCw P ℓ w0 δ θ) (fun j hj => (h1 j hj).2) ℓ le_rfl
  rw [hc0, cfoldUp_Enc hL (by omega) θ fs] at hchain
  have hcl : cchainCw P ℓ w0 δ θ ℓ = ev (lv L ℓ) (vpoly (P.g θ)) := by
    simp only [cchainCw, lt_irrefl, if_false]
    exact cW_last P w0 hℓ θ
  rw [hcl] at hchain
  haveI := lv_finite (L := L) ℓ
  have hd : 2 ^ m ≤ Nat.card (lv L ℓ) := by
    rw [← Nd_last (ℓ := ℓ)]; exact Nd_le_card hL (by omega)
  have := ev_injOn hd (vpoly_mem_degreeLT (P.g θ)) (vpoly_mem_degreeLT _) hchain
  rw [← ccoeffs_vpoly (P.g θ), this, ccoeffs_vpoly]

end Chain

/-! ### Lemma 2.1 for affine polynomials -/

/-- **Lemma 2.1 (root counting), as used in Theorem 6.13:** two distinct polynomials of degree
`≤ 1` agree on at most one point. -/
lemma card_agree_le_one [Fintype F] [DecidableEq F] (p q : F[X]) (hpq : p ≠ q)
    (hp : p.natDegree ≤ 1) (hq : q.natDegree ≤ 1) :
    (univ.filter fun c : F => p.eval c = q.eval c).card ≤ 1 := by
  have hne : p - q ≠ 0 := sub_ne_zero.mpr hpq
  calc (univ.filter fun c : F => p.eval c = q.eval c).card
      ≤ (p - q).roots.toFinset.card := by
        apply card_le_card
        intro c hc
        simp only [mem_filter, mem_univ, true_and] at hc
        simp [Multiset.mem_toFinset, mem_roots hne, IsRoot, hc]
    _ ≤ Multiset.card (p - q).roots := Multiset.toFinset_card_le _
    _ ≤ (p - q).natDegree := card_roots' _
    _ ≤ max p.natDegree q.natDegree := natDegree_sub_le _ _
    _ ≤ 1 := max_le hp hq

/-! ### Theorem 6.13 (soundness) -/

section Theorem

variable {L : Subgroup Fˣ} {m : ℕ} (P : SumProver F L m) (ℓ : ℕ) (w0 : L → F) (zp : ℕ → F)
  (zs : Fin m → F) (v : F) (δ : ℚ)

/-- The honest round polynomials `s*_{j+1}` for the decoded table `f*` of `w₀`. -/
noncomputable def csStar (θ : ℕ → F) (j : ℕ) : F[X] :=
  hS zs ℓ θ zp (cdecTable L (m + ℓ) δ w0) j

/-- The honest running values `v*_j = P_{f*_j}(z_{>j})`. -/
noncomputable def cvStar (θ : ℕ → F) (j : ℕ) : F :=
  hV zs ℓ θ zp (cdecTable L (m + ℓ) δ w0) j

/-- The bad event `E_{j+1}`, folding part: `θ_{j+1}` is not good for `w_j`. -/
def cBadFold (θ : ℕ → F) (j : ℕ) : Prop := ¬ cGoodAt ℓ δ m j (P.W ℓ w0 θ j) (θ j)

/-- The bad event `E_{j+1}`, restriction part: `s_{j+1} ≠ s*_{j+1}` and
`s_{j+1}(θ_{j+1}) = s*_{j+1}(θ_{j+1})`. -/
def BadRestr (θ : ℕ → F) (j : ℕ) : Prop :=
  P.s j θ ≠ csStar ℓ w0 zp zs δ θ j ∧
    (P.s j θ).eval (θ j) = (csStar ℓ w0 zp zs δ θ j).eval (θ j)

variable {P ℓ w0 zp zs v δ}

/-- Proof of Theorem 6.13, "No bad event", case 1. -/
theorem cno_bad_far {R : ℕ} (hL : IsSmoothDomain L (m + ℓ + R)) (hℓ : 1 ≤ ℓ)
    (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2)
    (hfar : ¬ FibDistLE w0 (RS L (2 ^ (m + ℓ)) : Set (L → F)) δ) (θ : ℕ → F)
    (hgood : ∀ j < ℓ, ¬ cBadFold P ℓ w0 δ θ j) :
    cpassFrac (P := P) (ℓ := ℓ) (w0 := w0) θ ≤ 1 - δ := by
  by_contra hπ
  push_neg at hπ
  exact hfar (cchain_final hL hℓ hδ θ (fun j hj => not_not.1 (hgood j hj)) hπ).1

/-- Proof of Theorem 6.13, "No bad event", case 2: if no bad event occurs and the restriction
and closure checks pass, then `π(θ) ≤ 1 - δ`. -/
theorem cno_bad_close {R : ℕ} (hL : IsSmoothDomain L (m + ℓ + R)) (hℓ : 1 ≤ ℓ)
    (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2)
    (hwrong : cpoly (cdecTable L (m + ℓ) δ w0) (catPt ℓ zp zs) ≠ v) (θ : ℕ → F)
    (hgood : ∀ j < ℓ, ¬ cBadFold P ℓ w0 δ θ j)
    (hres : ∀ j < ℓ, ¬ BadRestr P ℓ w0 zp zs δ θ j)
    (hR : P.RestrOK ℓ zp v θ) (hCl : P.ClosureOK ℓ zs v θ) :
    cpassFrac (P := P) (ℓ := ℓ) (w0 := w0) θ ≤ 1 - δ := by
  by_contra hπ
  push_neg at hπ
  have hg := (cchain_final hL hℓ hδ θ (fun j hj => not_not.1 (hgood j hj)) hπ).2
  set fs := cdecTable L (m + ℓ) δ w0
  -- `v_j ≠ v*_j` for all `j ≤ ℓ`
  have key : ∀ j ≤ ℓ, P.vv v θ j ≠ cvStar ℓ w0 zp zs δ θ j := by
    intro j hj
    induction j with
    | zero =>
      simp only [SumProver.vv, cvStar, hV_zero]
      exact fun h => hwrong h.symm
    | succ j ih =>
      have ih := ih (by omega)
      have hne : P.s j θ ≠ csStar ℓ w0 zp zs δ θ j := by
        intro heq
        apply ih
        rw [← hR j (by omega), heq, csStar, cvStar, hS_zp zs ℓ θ zp fs j (by omega)]
      have hev : (P.s j θ).eval (θ j) ≠ (csStar ℓ w0 zp zs δ θ j).eval (θ j) :=
        fun h => hres j (by omega) ⟨hne, h⟩
      simp only [SumProver.vv]
      rwa [csStar, hS_eval zs ℓ θ zp fs j (by omega)] at hev
  apply key ℓ le_rfl
  rw [hCl, hg, cvStar, hV_last]

/-- The core of the probability estimate of Theorem 6.13: if acceptance implies that a bad event
`B` occurs or that `π(θ) ≤ 1-δ`, then `Pr[V accepts] ≤ Pr[B] + (1-δ)^κ` (Lemma 3.3). -/
theorem csumAccProb_le_of [Fintype F] [Fintype L] (κ : ℕ) (B : (ℕ → F) → Prop) (hδ1 : δ ≤ 1)
    (hacc : ∀ θ : ℕ → F, P.RestrOK ℓ zp v θ → P.ClosureOK ℓ zs v θ → ¬ B θ →
      cpassFrac (P := P) (ℓ := ℓ) (w0 := w0) θ ≤ 1 - δ) :
    sumAccProb P ℓ κ w0 zp zs v ≤
      prob (fun θ : Fin ℓ → F => B (extR θ)) + (1 - δ) ^ κ := by
  classical
  haveI : Nonempty L := ⟨1⟩
  let S : (Fin ℓ → F) → Finset L := fun ρ =>
    (Set.toFinite (cPass P ℓ w0 (extR ρ) 0)).toFinset
  let A : (Fin ℓ → F) → Prop := fun ρ => cpassFrac (P := P) (ℓ := ℓ) (w0 := w0) (extR ρ) ≤ 1 - δ
  have hq := (independent_queries_le κ S A (1 - δ) (by linarith) ?_)
  · calc sumAccProb P ℓ κ w0 zp zs v
        ≤ prob (fun ω : (Fin ℓ → F) × (Fin κ → L) =>
            B (extR ω.1) ∨ (A ω.1 ∧ ∀ t, ω.2 t ∈ S ω.1)) := by
          apply prob_mono
          rintro ⟨ρ, ξ⟩ ⟨hR, hCl, hQ⟩
          by_cases hB : B (extR ρ)
          · exact Or.inl hB
          · refine Or.inr ⟨hacc _ hR hCl hB, fun t => ?_⟩
            simp only [S, Set.Finite.mem_toFinset]
            exact (cmem_Pass_zero _ _).2 (hQ t).1
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
    simp only [A, cpassFrac] at hA
    rwa [div_le_iff₀ hpos] at hA

/-- Per-round count for the folding part of the bad events (Lemma 6.9 at level `j+1`). -/
theorem card_cbadFold_le [Fintype F] [DecidableEq F] {R : ℕ} (hL : IsSmoothDomain L (m + ℓ + R))
    (hδ0 : 0 < δ) (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2) {j : ℕ} (hj : j < ℓ) (w : lv L j → F) :
    {c : F | ¬ cGoodAt ℓ δ m j w c}.ncard ≤ Nat.card (lv L (j + 1)) := by
  obtain ⟨hDj, hμj, hdD, hrate⟩ := level_facts hL hj
  have hδj : δ ≤ (1 - rate (sqDom (lv L j)) (Nd m ℓ (j + 1))) / 2 := by rw [hrate]; exact hδ
  exact ncard_not_cgood_le hDj hμj (Nd_pos _ _ _) hdD hδ0 hδj w

/-- **Theorem 6.13(1) (soundness, far commitment).** Let `1 ≤ ℓ`, `L` a smooth domain of order
`M = 2^{n+R}`, `0 < δ ≤ (1-ρ)/2`, and let the prover be causal.  If `Δ^fib₀(w₀, 𝒞₀) > δ`, the
verifier accepts with probability at most `ε_fold + (1-δ)^κ`. -/
theorem csoundness_far [Fintype F] [DecidableEq F] [Fintype L] {R : ℕ}
    (hL : IsSmoothDomain L (m + ℓ + R)) (hℓ : 1 ≤ ℓ) (hδ0 : 0 < δ)
    (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2) (hC : P.Causal) (κ : ℕ)
    (hfar : ¬ FibDistLE w0 (RS L (2 ^ (m + ℓ)) : Set (L → F)) δ) :
    sumAccProb P ℓ κ w0 zp zs v ≤ epsFold F (m + ℓ + R) ℓ + (1 - δ) ^ κ := by
  classical
  have hR : (0 : ℚ) < 1 / 2 ^ R := by positivity
  refine (csumAccProb_le_of κ (fun θ => ∃ j < ℓ, cBadFold P ℓ w0 δ θ j) (by linarith)
    (fun θ _ _ hB => cno_bad_far hL hℓ hδ hfar θ (fun j hj h => hB ⟨j, hj, h⟩))).trans ?_
  apply add_le_add_right
  let E : Fin ℓ → (Fin ℓ → F) → Prop := fun i ρ => cBadFold P ℓ w0 δ (extR ρ) i
  have hseq := sequential_challenges (Ch := fun _ : Fin ℓ => F) E
    (fun i => (Nat.card (lv L ((i : ℕ) + 1)) : ℚ)) ?_
  · calc prob (fun ρ : Fin ℓ → F => ∃ j < ℓ, cBadFold P ℓ w0 δ (extR ρ) j)
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
        ¬ cGoodAt ℓ δ m i (P.W ℓ w0 (extR ρ) i) c := by
      intro c
      simp only [E, cBadFold, extR_update]
      rw [cW_congr P w0 hC i.isLt (fun k hk => Function.update_of_ne (by omega) _ _),
        Function.update_self]
    simp_rw [hE]
    rw [card_filter_eq_ncard]
    exact_mod_cast card_cbadFold_le hL hδ0 hδ i.isLt _

/-- **Theorem 6.13(2) (soundness, wrong value).** Under the hypotheses of `csoundness_far`, and
with affine round polynomials: if the decoded table `f*` of `w₀` satisfies `P_{f*}(z) ≠ v`, the
verifier accepts with probability at most `ε_fold + ℓ/|F| + (1-δ)^κ`.  (The paper also assumes
`Δ^fib₀(w₀, 𝒞₀) ≤ δ`; the bound holds without it.) -/
theorem csoundness_close [Fintype F] [DecidableEq F] [Fintype L] {R : ℕ}
    (hL : IsSmoothDomain L (m + ℓ + R)) (hℓ : 1 ≤ ℓ) (hδ0 : 0 < δ)
    (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2) (hC : P.Causal) (hdeg : P.DegOK) (κ : ℕ)
    (hwrong : cpoly (cdecTable L (m + ℓ) δ w0) (catPt ℓ zp zs) ≠ v) :
    sumAccProb P ℓ κ w0 zp zs v ≤
      epsFold F (m + ℓ + R) ℓ + ℓ / Fintype.card F + (1 - δ) ^ κ := by
  classical
  have hR : (0 : ℚ) < 1 / 2 ^ R := by positivity
  refine (csumAccProb_le_of κ
    (fun θ => ∃ j < ℓ, cBadFold P ℓ w0 δ θ j ∨ BadRestr P ℓ w0 zp zs δ θ j)
    (by linarith) (fun θ hRs hCl hB => cno_bad_close hL hℓ hδ hwrong θ
      (fun j hj h => hB ⟨j, hj, Or.inl h⟩) (fun j hj h => hB ⟨j, hj, Or.inr h⟩) hRs hCl)).trans ?_
  apply add_le_add_right
  let E : Fin ℓ → (Fin ℓ → F) → Prop := fun i ρ =>
    cBadFold P ℓ w0 δ (extR ρ) i ∨ BadRestr P ℓ w0 zp zs δ (extR ρ) i
  have hseq := sequential_challenges (Ch := fun _ : Fin ℓ => F) E
    (fun i => (Nat.card (lv L ((i : ℕ) + 1)) : ℚ) + 1) ?_
  · calc prob (fun ρ : Fin ℓ → F =>
          ∃ j < ℓ, cBadFold P ℓ w0 δ (extR ρ) j ∨ BadRestr P ℓ w0 zp zs δ (extR ρ) j)
        ≤ prob (fun ρ : Fin ℓ → F => ∃ i, E i ρ) := by
          apply prob_mono
          rintro ρ ⟨j, hj, h⟩
          exact ⟨⟨j, hj⟩, h⟩
      _ ≤ _ := hseq
      _ = epsFold F (m + ℓ + R) ℓ + ℓ / Fintype.card F := by
          rw [epsFold, ← Fin.sum_univ_eq_sum_range]
          simp only [add_div, sum_add_distrib]
          congr 1
          · refine sum_congr rfl (fun i _ => ?_)
            rw [card_lv hL (by omega)]; push_cast; rfl
          · simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  · intro i ρ
    set θ := extR ρ
    have hupd : ∀ c : F, ∀ k < (i : ℕ), Function.update θ i c k = θ k :=
      fun c k hk => Function.update_of_ne (by omega) _ _
    have hE : ∀ c : F, E i (Function.update ρ i c) ↔
        (¬ cGoodAt ℓ δ m i (P.W ℓ w0 θ i) c ∨
          (P.s i θ ≠ csStar ℓ w0 zp zs δ θ i ∧
            (P.s i θ).eval c = (csStar ℓ w0 zp zs δ θ i).eval c)) := by
      intro c
      simp only [E, cBadFold, BadRestr, extR_update, csStar]
      rw [cW_congr P w0 hC i.isLt (hupd c), hC.1 i _ θ (hupd c),
        hS_congr zs ℓ _ θ zp _ i (hupd c), Function.update_self]
    simp_rw [hE]
    rw [filter_or]
    refine (Nat.cast_le.2 (card_union_le _ _)).trans ?_
    push_cast
    apply add_le_add
    · rw [card_filter_eq_ncard]
      exact_mod_cast card_cbadFold_le hL hδ0 hδ i.isLt _
    · by_cases hne : P.s i θ ≠ csStar ℓ w0 zp zs δ θ i
      · simp only [hne, ne_eq, not_false_eq_true, true_and]
        exact_mod_cast card_agree_le_one _ _ hne (hdeg i θ) (natDegree_hS zs ℓ θ zp _ i)
      · simp [hne]

/-- **Corollary 6.14 (evaluation binding).** Let `1 ≤ ℓ` and `ε = ε_fold + ℓ/|F| + (1-δ)^κ`.
If some causal prover with affine round polynomials makes the verifier accept `(w₀; z, v)` with
probability greater than `ε`, then `Δ^fib₀(w₀, 𝒞₀) ≤ δ` and `v = P_{f*}(z)` for the decoded
table `f*` of `w₀`.  (Randomised provers reduce to deterministic ones by Lemma 3.4.) -/
theorem ceval_binding [Fintype F] [DecidableEq F] [Fintype L] {R : ℕ}
    (hL : IsSmoothDomain L (m + ℓ + R)) (hℓ : 1 ≤ ℓ) (hδ0 : 0 < δ)
    (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2) (hC : P.Causal) (hdeg : P.DegOK) (κ : ℕ)
    (hacc : epsFold F (m + ℓ + R) ℓ + ℓ / Fintype.card F + (1 - δ) ^ κ
      < sumAccProb P ℓ κ w0 zp zs v) :
    FibDistLE w0 (RS L (2 ^ (m + ℓ)) : Set (L → F)) δ ∧
      v = cpoly (cdecTable L (m + ℓ) δ w0) (catPt ℓ zp zs) := by
  have hF : (0 : ℚ) ≤ ℓ / Fintype.card F := by positivity
  constructor
  · by_contra hfar
    have := csoundness_far (v := v) (zp := zp) (zs := zs) hL hℓ hδ0 hδ hC κ hfar
    linarith
  · by_contra hne
    have := csoundness_close hL hℓ hδ0 hδ hC hdeg κ (fun h => hne h.symm)
    linarith

/-- **Corollary 6.14, "in particular":** `Π_eval` is `ε`-evaluation binding (Definition 3.11). -/
theorem ceval_binding' [Fintype F] [DecidableEq F] [Fintype L] {R : ℕ}
    (hL : IsSmoothDomain L (m + ℓ + R)) (hℓ : 1 ≤ ℓ) (hδ0 : 0 < δ)
    (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2) (κ : ℕ) {v' : F} (hvv : v ≠ v')
    (P' : SumProver F L m) (hC : P.Causal) (hdeg : P.DegOK) (hC' : P'.Causal)
    (hdeg' : P'.DegOK) :
    ¬ (epsFold F (m + ℓ + R) ℓ + ℓ / Fintype.card F + (1 - δ) ^ κ
          < sumAccProb P ℓ κ w0 zp zs v ∧
        epsFold F (m + ℓ + R) ℓ + ℓ / Fintype.card F + (1 - δ) ^ κ
          < sumAccProb P' ℓ κ w0 zp zs v') := by
  rintro ⟨h1, h2⟩
  have e1 := (ceval_binding hL hℓ hδ0 hδ hC hdeg κ h1).2
  have e2 := (ceval_binding hL hℓ hδ0 hδ hC' hdeg' κ h2).2
  exact hvv (e1.trans e2.symm)

end Theorem

/-! ### Corollary 6.15 (the sum protocol) -/

/-- **Corollary 6.15 (soundness and binding of `Π_sum`).** With `z = (1, …, 1)`: if the decoded
table `f*` of `w₀` satisfies `∑_a f*(a) ≠ v`, the verifier of `Π_sum` accepts with probability at
most `ε_fold + ℓ/|F| + (1-δ)^κ`; equivalently, acceptance with larger probability forces
`v = ∑_a f*(a)`. -/
theorem soundness_sum [Fintype F] [DecidableEq F] {L : Subgroup Fˣ} [Fintype L] {m ℓ R : ℕ}
    (P : SumProver F L m) (w0 : L → F) (v : F) {δ : ℚ}
    (hL : IsSmoothDomain L (m + ℓ + R)) (hℓ : 1 ≤ ℓ) (hδ0 : 0 < δ)
    (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2) (hC : P.Causal) (hdeg : P.DegOK) (κ : ℕ)
    (hwrong : ∑ a, cdecTable L (m + ℓ) δ w0 a ≠ v) :
    sumAccProb P ℓ κ w0 (fun _ => 1) (fun _ => 1) v ≤
      epsFold F (m + ℓ + R) ℓ + ℓ / Fintype.card F + (1 - δ) ^ κ := by
  refine csoundness_close hL hℓ hδ0 hδ hC hdeg κ ?_
  rw [catPt_one, cpoly_one]
  exact hwrong

/-- **Corollary 6.15, binding form.** -/
theorem sum_binding [Fintype F] [DecidableEq F] {L : Subgroup Fˣ} [Fintype L] {m ℓ R : ℕ}
    (P : SumProver F L m) (w0 : L → F) (v : F) {δ : ℚ}
    (hL : IsSmoothDomain L (m + ℓ + R)) (hℓ : 1 ≤ ℓ) (hδ0 : 0 < δ)
    (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2) (hC : P.Causal) (hdeg : P.DegOK) (κ : ℕ)
    (hacc : epsFold F (m + ℓ + R) ℓ + ℓ / Fintype.card F + (1 - δ) ^ κ
      < sumAccProb P ℓ κ w0 (fun _ => 1) (fun _ => 1) v) :
    FibDistLE w0 (RS L (2 ^ (m + ℓ)) : Set (L → F)) δ ∧
      v = ∑ a, cdecTable L (m + ℓ) δ w0 a := by
  obtain ⟨h1, h2⟩ := ceval_binding hL hℓ hδ0 hδ hC hdeg κ hacc
  refine ⟨h1, ?_⟩
  rw [h2, catPt_one, cpoly_one]

/-! ### Proposition 6.16 (the case `ℓ = 0`) -/

section NoFolding

variable {L : Subgroup Fˣ} {m : ℕ}

/-- For `ℓ = 0`, the verifier accepts iff `v = P_g(z)` and every query point lies in
`S = {ξ ∈ L : w₀(ξ) = V_g(ξ)}`. -/
lemma caccepts_zero (P : SumProver F L m) (w0 : L → F) (zp : ℕ → F) (zs : Fin m → F) (v : F)
    {κ : ℕ} (θ : ℕ → F) (ξ : Fin κ → L) :
    P.Accepts 0 w0 zp zs v θ ξ ↔
      v = cpoly (P.g θ) zs ∧ ∀ t, w0 (ξ t) = (vpoly (P.g θ)).eval (((ξ t : L) : Fˣ) : F) := by
  simp [SumProver.Accepts, SumProver.RestrOK, SumProver.ClosureOK, SumProver.QueryOK,
    SumProver.vv]

/-- **Proposition 6.16 (no folding).** Let `ℓ = 0`, `L` a smooth domain of order `2^{n+R}`
(`n = m`), `δ ≤ (1-ρ)/2`.  If a deterministic prover makes the verifier accept `(w₀; z, v)` with
probability greater than `(1-δ)^κ`, then its (fixed) final table `g` satisfies
`Δ(w₀, Enc(g)) < δ`, `v = P_g(z)`, and `g` is the unique table with `Δ(w₀, Enc(g)) ≤ δ`. -/
theorem cno_folding [Fintype F] [DecidableEq F] [Fintype L] {R : ℕ}
    (hL : IsSmoothDomain L (m + R)) {δ : ℚ} (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2) (κ : ℕ)
    (P : SumProver F L m) (w0 : L → F) (zp : ℕ → F) (zs : Fin m → F) (v : F)
    (hacc : (1 - δ) ^ κ < sumAccProb P 0 κ w0 zp zs v) :
    relDist w0 (cEnc L (P.g fun _ => 0)) < δ ∧ v = cpoly (P.g fun _ => 0) zs ∧
      ∀ f : Table F m, relDist w0 (cEnc L f) ≤ δ → f = P.g fun _ => 0 := by
  classical
  haveI : Nonempty L := ⟨1⟩
  set g0 := P.g fun _ => 0
  have hR : (0 : ℚ) < 1 / 2 ^ R := by positivity
  let S : Finset L := univ.filter (fun ξ => w0 ξ = (vpoly g0).eval (((ξ : L) : Fˣ) : F))
  let A : Prop := v = cpoly g0 zs
  have hev : (fun ω : (Fin 0 → F) × (Fin κ → L) => P.Accepts 0 w0 zp zs v (extR ω.1) ω.2) =
      fun ω => (fun _ : Fin 0 → F => A) ω.1 ∧ ∀ t, ω.2 t ∈ (fun _ : Fin 0 → F => S) ω.1 := by
    funext ω
    rw [caccepts_zero, extR_zero]
    simp [S, A, g0]
  have hq := independent_queries (Ω' := Fin 0 → F) κ (fun _ => S) (fun _ => A)
  rw [sumAccProb, hev, hq] at hacc
  simp only [expect, Fintype.univ_ofSubsingleton, sum_singleton, Fintype.card_unique,
    Nat.cast_one, div_one] at hacc
  by_cases hA : A
  · rw [if_pos hA] at hacc
    have hM : (0 : ℚ) < Fintype.card L := by exact_mod_cast Fintype.card_pos
    have hSM : 1 - δ < (S.card : ℚ) / Fintype.card L := by
      by_contra hle
      push_neg at hle
      have h1 : (0 : ℚ) ≤ 1 - δ := by linarith
      have := pow_le_pow_left₀ (by positivity) hle κ
      linarith
    have hagree : agreeSet w0 (cEnc L g0) = (S : Set L) := by
      ext ξ; simp [agreeSet, S, cEnc, ev]
    have hdist : relDist w0 (cEnc L g0) < δ := by
      have h := agree_add_hdist w0 (cEnc L g0)
      rw [hagree, Set.ncard_coe_finset] at h
      have h' : (S.card : ℚ) + hdist w0 (cEnc L g0) = Nat.card L := by exact_mod_cast h
      rw [Nat.card_eq_fintype_card] at h'
      unfold relDist
      rw [Nat.card_eq_fintype_card, div_lt_iff₀ hM]
      rw [lt_div_iff₀ hM] at hSM
      linarith
    refine ⟨hdist, hA, fun f hf => ?_⟩
    have hrate : rate L (2 ^ m) = 1 / 2 ^ R := rate_lv (ℓ := 0) hL (j := 0) (by omega)
    have hδ' : δ ≤ (1 - rate L (2 ^ m)) / 2 := by rw [hrate]; exact hδ
    haveI := hL.finite
    have := RS_unique_decoding' δ hδ' w0 (cEnc_mem_RS L f) (cEnc_mem_RS L g0) hf hdist.le
    exact cEnc_injective (show 2 ^ m ≤ Nat.card L from Nd_le_card (ℓ := 0) hL (j := 0) (by omega))
      this
  · rw [if_neg hA] at hacc
    have : (0 : ℚ) ≤ (1 - δ) ^ κ := pow_nonneg (by linarith) κ
    linarith

end NoFolding

end SumFRI
