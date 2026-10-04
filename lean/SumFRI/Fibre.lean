/-
SumFRI/Fibre.lean
§6.1–6.3 of the Sum-FRI paper, for one classical folding step on a smooth domain `D` (the paper's
`L_{j-1}`, with `L_j = D²`):
* Definition 6.4 (decoded table, monomial basis) `ccoeffs`, `cdecTable`, `cdecTable_spec`, with
  the coefficient-vector facts `coeff_vpoly`, `vpoly_mem_degreeLT`, `ccoeffs_vpoly`,
  `vpoly_ccoeffs`, and Lemma 5.2 (encoding) `cEnc_mem_RS`, `cEnc_injective`;
* Lemma 4.8 (classical word fold), the facts used below: `cwfold_congr`, `cwfold_mem_RS`;
* Lemma 6.6 (folding far words) `cfar_fold`, from the axiom `bciks_unique` applied directly to
  the line `cfold_θ(w) = w_e + θ w_o`;
* Lemma 6.7 (fibre errors survive folding) `csurvive_eq`, `csurvive`;
* Definition 6.8 (good challenge) `CGood`; Lemma 6.9 (few bad challenges) `ncard_not_cgood_le`;
* Lemma 6.10 (one folding step) `cone_step`.

The fibre distance, the decoded codeword and unique fibre decoding (Definition 6.1, Lemmas 6.2,
6.3) do not involve the fold and are those of `KBFold/Fibre.lean` (`fibDist`, `FibDistLE`,
`dec`, `dec_spec`, `fib_unique`).  Conventions are those of `KBFold/Fibre.lean`.
-/
import SumFRI.Scheme
import KBFold.Fibre

set_option autoImplicit false

open Polynomial

namespace SumFRI

open KBFold

variable {F : Type*} [Field F]

/-! ### Coefficient vectors (Lemma 5.2 and Definition 6.4) -/

section Coefficients

/-- The coefficients of `V_f`: `[X^k] V_f = f(a)` if `k` is the integer with bit vector `a`,
and `0` if `k ≥ 2^n`. -/
theorem coeff_vpoly {n : ℕ} (f : Table F n) (k : ℕ) :
    (vpoly f).coeff k = ∑ a, if k = bitsToNat a then f a else 0 := by
  unfold vpoly
  rw [finset_sum_coeff]
  simp only [coeff_C_mul_X_pow]

/-- `V_f ∈ F[X]_{<2^n}`. -/
theorem vpoly_mem_degreeLT {n : ℕ} (f : Table F n) : vpoly f ∈ degreeLT F (2 ^ n) := by
  rw [mem_degreeLT, degree_lt_iff_coeff_zero]
  intro k hk
  rw [coeff_vpoly]
  refine Finset.sum_eq_zero (fun a _ => ?_)
  rw [if_neg]
  have := bitsToNat_lt a
  omega

/-- The table of coefficients `a ↦ [X^a] P` of a polynomial (Lemma 5.2). -/
noncomputable def ccoeffs (n : ℕ) (P : F[X]) : Table F n := fun a => P.coeff (bitsToNat a)

/-- Lemma 5.2: the coefficient vector of `V_f` is `f`. -/
theorem ccoeffs_vpoly {n : ℕ} (f : Table F n) : ccoeffs n (vpoly f) = f := by
  funext a
  show (vpoly f).coeff (bitsToNat a) = f a
  rw [coeff_vpoly, Finset.sum_eq_single a]
  · rw [if_pos rfl]
  · intro b _ hb
    rw [if_neg]
    intro h
    exact hb (bitsToNat_injective h).symm
  · intro h
    exact absurd (Finset.mem_univ a) h

/-- Lemma 5.2: every `P ∈ F[X]_{<2^n}` is `V_f` for its coefficient vector `f`. -/
theorem vpoly_ccoeffs {n : ℕ} {P : F[X]} (hP : P ∈ degreeLT F (2 ^ n)) :
    vpoly (ccoeffs n P) = P := by
  ext k
  rw [coeff_vpoly]
  by_cases hk : k < 2 ^ n
  · obtain ⟨a, ha⟩ := (bitsToNat_bijective n).2 ⟨k, hk⟩
    have ha' : bitsToNat a = k := congrArg Fin.val ha
    rw [Finset.sum_eq_single a]
    · rw [if_pos ha'.symm]
      show P.coeff (bitsToNat a) = P.coeff k
      rw [ha']
    · intro b _ hb
      rw [if_neg]
      intro h
      exact hb (bitsToNat_injective (h.symm.trans ha'.symm))
    · intro h
      exact absurd (Finset.mem_univ a) h
  · rw [Finset.sum_eq_zero]
    · rw [mem_degreeLT, degree_lt_iff_coeff_zero] at hP
      exact (hP k (by omega)).symm
    · intro a _
      rw [if_neg]
      have := bitsToNat_lt a
      omega

variable {L : Subgroup Fˣ}

/-- Lemma 5.2: `Enc(f) ∈ 𝒞₀ = RS[L, 2^n]`. -/
theorem cEnc_mem_RS (L : Subgroup Fˣ) {n : ℕ} (f : Table F n) : cEnc L f ∈ RS L (2 ^ n) :=
  ev_mem_RS (vpoly_mem_degreeLT f)

/-- Lemma 5.2: if `2^n ≤ |L|`, `Enc` is injective. -/
theorem cEnc_injective [Finite L] {n : ℕ} (hn : 2 ^ n ≤ Nat.card L) :
    Function.Injective (cEnc L (n := n) (F := F)) := by
  intro f f' h
  have := ev_injOn hn (vpoly_mem_degreeLT f) (vpoly_mem_degreeLT f') h
  rw [← ccoeffs_vpoly f, this, ccoeffs_vpoly]

/-- **Definition 6.4 (decoded table).** The coefficient vector `f*` of `P_{dec₀(w)}`, i.e. the
unique table with `Enc(f*) = dec₀(w)` (`cdecTable_spec`). -/
noncomputable def cdecTable (L : Subgroup Fˣ) (n : ℕ) (δ : ℚ) (w : L → F) : Table F n :=
  ccoeffs n (polyOf (dec (RS L (2 ^ n) : Set (L → F)) δ w))

/-- Definition 6.4: if `Δ^fib₀(w, 𝒞₀) ≤ δ`, then `Enc(f*) = dec₀(w)`. -/
theorem cdecTable_spec [Finite L] {n : ℕ} (hn : 2 ^ n ≤ Nat.card L) {δ : ℚ} {w : L → F}
    (h : FibDistLE w (RS L (2 ^ n) : Set (L → F)) δ) :
    cEnc L (cdecTable L n δ w) = dec (RS L (2 ^ n) : Set (L → F)) δ w := by
  obtain ⟨hP, hPc⟩ := polyOf_spec hn (dec_spec h).1
  rw [cEnc, cdecTable, vpoly_ccoeffs hP, hPc]

end Coefficients

/-! ### Facts on the classical word fold (Lemma 4.8) -/

section WordFacts

variable {D : Subgroup Fˣ}

lemma evenW_sub' (w c : D → F) (η : sqDom D) : evenW (w - c) η = evenW w η - evenW c η := by
  simp only [evenW, Pi.sub_apply]; ring

lemma oddW_sub' (w c : D → F) (η : sqDom D) : oddW (w - c) η = oddW w η - oddW c η := by
  simp only [oddW, Pi.sub_apply]; ring

/-- Lemma 4.8(1) (locality): `cfold_θ(w)(η)` depends only on `w` on the fibre over `η`. -/
theorem cwfold_congr (θ : F) {w w' : D → F} {η : sqDom D} (h : ∀ ξ ∈ fibre η, w ξ = w' ξ) :
    cwfold θ w η = cwfold θ w' η := by
  simp only [cwfold, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [evenW_congr h, oddW_congr h]

/-- Lemma 4.8(4): `cfold_θ` maps `RS[D, 2d]` into `RS[D², d]`. -/
theorem cwfold_mem_RS (hD : (-1 : Fˣ) ∈ D) (h2 : (2 : F) ≠ 0) (θ : F) {d : ℕ} {c : D → F}
    (hc : c ∈ RS D (2 * d)) : cwfold θ c ∈ RS (sqDom D) d := by
  obtain ⟨U, hU, rfl⟩ := mem_RS.1 hc
  rw [cwfold_ev hD h2]
  exact ev_mem_RS (cfold_mem_degreeLT θ hU)

end WordFacts

/-! ### Lemmas 6.6 and 6.7 (two folding lemmas for the classical fold) -/

section Folding

variable {D : Subgroup Fˣ}

/-- **Lemma 6.6 (folding far words).** Let `D` be a smooth domain of order `2^μ` with `μ ≥ 1`,
`1 ≤ d` with `2d ≤ |D|`, and `0 < δ ≤ (1-ρ)/2`.  If `Δ^fib(w, RS[D,2d]) > δ`, then at most
`|D²|` values `θ ∈ F` satisfy `Δ(cfold_θ(w), RS[D²,d]) ≤ δ`.  (Proof: the axiom `bciks_unique`
applied to the line `cfold_θ(w) = w_e + θ w_o`, Lemma 4.8(2).) -/
theorem cfar_fold [Fintype F] {μ : ℕ} (hD : IsSmoothDomain D μ) (hμ : 1 ≤ μ) {d : ℕ}
    (hd : 1 ≤ d) (hdD : 2 * d ≤ Nat.card D) {δ : ℚ} (hδ0 : 0 < δ)
    (hδ : δ ≤ (1 - rate (sqDom D) d) / 2) (w : D → F)
    (hfar : ¬ FibDistLE w (RS D (2 * d) : Set (D → F)) δ) :
    {θ : F | DistLE (cwfold θ w) (RS (sqDom D) d : Set (sqDom D → F)) δ}.ncard
      ≤ Nat.card (sqDom D) := by
  haveI := hD.finite
  have hneg : (-1 : Fˣ) ∈ D := hD.neg_one_mem hμ
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_smooth hD hμ
  have hM := card_eq_two_mul_sqDom hneg h2
  by_contra hlt
  push_neg at hlt
  obtain ⟨L', hL', c0, hc0, c1, hc1, hagree⟩ :=
    bciks_unique (sqDom D) (μ - 1) (hD.sqDom_smooth hμ) d hd (by omega) δ hδ0 hδ
      (evenW w) (oddW w) hlt
  have hdD' : d ≤ Nat.card (sqDom D) := by omega
  obtain ⟨hP0, hP0c⟩ := polyOf_spec hdD' hc0
  obtain ⟨hP1, hP1c⟩ := polyOf_spec hdD' hc1
  set T : F[X] := expand F 2 (polyOf c0) + X * expand F 2 (polyOf c1)
  have hE : evenPart T = polyOf c0 := (even_odd_unique (polyOf c0) (polyOf c1)).1
  have hO : oddPart T = polyOf c1 := (even_odd_unique (polyOf c0) (polyOf c1)).2
  have hT : T ∈ degreeLT F (2 * d) := mem_degreeLT_of_parts (by rw [hE]; exact hP0)
    (by rw [hO]; exact hP1)
  apply hfar
  refine ⟨ev D T, ev_mem_RS hT, (fibDist_le_iff _ _ δ).2 ⟨L', hL', ?_⟩⟩
  intro η hη ξ hξ
  rw [mem_fibre] at hξ
  obtain ⟨h0, h1⟩ := hagree η hη
  have he : evenW w η = (polyOf c0).eval ((η : Fˣ) : F) := by
    rw [h0, ← congrFun hP0c η]; rfl
  have ho : oddW w η = (polyOf c1).eval ((η : Fˣ) : F) := by
    rw [h1, ← congrFun hP1c η]; rfl
  rw [eval_pos_split hneg h2 w ξ, hξ, he, ho]
  simp only [ev]
  rw [eval_even_odd T, hE, hO, ← hξ, val_sqPt]

/-- **Lemma 6.7 (fibre errors survive folding)**, core form: if `w` and `c` differ somewhere on
the fibre over `η`, two challenges `θ, θ'` with `cfold_θ(w)(η) = cfold_θ(c)(η)` are equal. -/
theorem csurvive_eq (hD : (-1 : Fˣ) ∈ D) (h2 : (2 : F) ≠ 0) {w c : D → F} {η : sqDom D}
    (hη : ∃ ξ ∈ fibre η, w ξ ≠ c ξ) {θ θ' : F} (hθ : cwfold θ w η = cwfold θ c η)
    (hθ' : cwfold θ' w η = cwfold θ' c η) : θ = θ' := by
  have hlin : ∀ t : F, cwfold t w η - cwfold t c η = evenW (w - c) η + t * oddW (w - c) η := by
    intro t
    simp only [cwfold, Pi.add_apply, Pi.smul_apply, smul_eq_mul, evenW_sub', oddW_sub']
    ring
  have e1 : evenW (w - c) η + θ * oddW (w - c) η = 0 := by rw [← hlin, hθ, sub_self]
  have e2 : evenW (w - c) η + θ' * oddW (w - c) η = 0 := by rw [← hlin, hθ', sub_self]
  by_contra hne
  have hu1 : oddW (w - c) η = 0 := by
    have : (θ - θ') * oddW (w - c) η = 0 := by linear_combination e1 - e2
    rcases mul_eq_zero.1 this with h | h
    · exact absurd (sub_eq_zero.1 h) hne
    · exact h
  have hu0 : evenW (w - c) η = 0 := by rw [hu1, mul_zero, add_zero] at e1; exact e1
  obtain ⟨ξ, hξ, hne'⟩ := hη
  have := (vanish_fibre_iff hD h2 (w - c) η).2 ⟨hu0, hu1⟩ ξ hξ
  exact hne' (sub_eq_zero.1 this)

/-- **Lemma 6.7 (fibre errors survive folding).** If `w` and `c` differ somewhere on the fibre
over `η`, there is at most one `θ ∈ F` with `cfold_θ(w)(η) = cfold_θ(c)(η)`. -/
theorem csurvive (hD : (-1 : Fˣ) ∈ D) (h2 : (2 : F) ≠ 0) {w c : D → F} {η : sqDom D}
    (hη : ∃ ξ ∈ fibre η, w ξ ≠ c ξ) :
    {θ : F | cwfold θ w η = cwfold θ c η}.ncard ≤ 1 := by
  by_cases hfin : {θ : F | cwfold θ w η = cwfold θ c η}.Finite
  · exact (Set.ncard_le_one hfin).2 (fun θ hθ θ' hθ' => csurvive_eq hD h2 hη hθ hθ')
  · rw [Set.Infinite.ncard hfin]; exact zero_le_one

end Folding

/-! ### Definition 6.8, Lemmas 6.9 and 6.10 (good challenges, one folding step) -/

section Good

variable {D : Subgroup Fˣ}

/-- **Definition 6.8 (good challenge)** for the classical fold.  For a word `w` on `D`, codes
`𝒞 = RS[D,2d]` and `𝒞' = RS[D²,d]`: `θ` is good for `w` if
1. when `Δ^fib(w, 𝒞) > δ`: `Δ(cfold_θ(w), 𝒞') > δ`;
2. when `Δ^fib(w, 𝒞) ≤ δ`, with `c = dec(w)`: for every `η ∈ D²` over whose fibre `w` and `c`
   differ somewhere, `cfold_θ(w)(η) ≠ cfold_θ(c)(η)`. -/
def CGood (δ : ℚ) (d : ℕ) (w : D → F) (θ : F) : Prop :=
  (¬ FibDistLE w (RS D (2 * d) : Set (D → F)) δ →
      ¬ DistLE (cwfold θ w) (RS (sqDom D) d : Set (sqDom D → F)) δ) ∧
  (FibDistLE w (RS D (2 * d) : Set (D → F)) δ →
      ∀ η : sqDom D, (∃ ξ ∈ fibre η, w ξ ≠ dec (RS D (2 * d) : Set (D → F)) δ w ξ) →
        cwfold θ w η ≠ cwfold θ (dec (RS D (2 * d) : Set (D → F)) δ w) η)

/-- **Lemma 6.9 (few bad challenges).** At most `|D²|` values `θ ∈ F` are not good for `w`. -/
theorem ncard_not_cgood_le [Fintype F] {μ : ℕ} (hD : IsSmoothDomain D μ) (hμ : 1 ≤ μ) {d : ℕ}
    (hd : 1 ≤ d) (hdD : 2 * d ≤ Nat.card D) {δ : ℚ} (hδ0 : 0 < δ)
    (hδ : δ ≤ (1 - rate (sqDom D) d) / 2) (w : D → F) :
    {θ : F | ¬ CGood δ d w θ}.ncard ≤ Nat.card (sqDom D) := by
  classical
  haveI := hD.finite
  have hneg : (-1 : Fˣ) ∈ D := hD.neg_one_mem hμ
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_smooth hD hμ
  by_cases hfar : FibDistLE w (RS D (2 * d) : Set (D → F)) δ
  · set c := dec (RS D (2 * d) : Set (D → F)) δ w
    have hbad : ∀ θ ∈ {θ : F | ¬ CGood δ d w θ},
        ∃ η, η ∈ fibBad w c ∧ cwfold θ w η = cwfold θ c η := by
      intro θ hθ
      simp only [Set.mem_setOf_eq, CGood, not_and_or] at hθ
      rcases hθ with h | h
      · exact absurd (fun hf => (hf hfar).elim) h
      · by_contra hne
        push_neg at hne
        exact h (fun _ η hη => hne η hη)
    choose! f hf using hbad
    calc {θ : F | ¬ CGood δ d w θ}.ncard ≤ (fibBad w c).ncard :=
          Set.ncard_le_ncard_of_injOn f (fun θ hθ => (hf θ hθ).1)
            (fun θ hθ θ' hθ' he => csurvive_eq hneg h2 (hf θ hθ).1 (hf θ hθ).2
              (by rw [he]; exact (hf θ' hθ').2))
      _ ≤ Nat.card (sqDom D) := by
          rw [← Set.ncard_univ]; exact Set.ncard_le_ncard (Set.subset_univ _)
  · have hsub : {θ : F | ¬ CGood δ d w θ} ⊆
        {θ : F | DistLE (cwfold θ w) (RS (sqDom D) d : Set (sqDom D → F)) δ} := by
      intro θ hθ
      simp only [Set.mem_setOf_eq, CGood, not_and_or] at hθ
      rcases hθ with h | h
      · by_contra hne; exact h (fun _ => hne)
      · exact absurd (fun hf => absurd hf hfar) h
    exact (Set.ncard_le_ncard hsub (Set.toFinite _)).trans
      (cfar_fold hD hμ hd hdD hδ0 hδ w hfar)

/-- **Lemma 6.10 (one folding step).** Let `θ` be good for `w`, `c' ∈ RS[D²,d]` and
`Y = {η ∈ D² : cfold_θ(w)(η) = c'(η)}` with `|Y| ≥ (1-δ)|D²|`.  Then `Δ^fib(w, 𝒞) ≤ δ`, the
codeword `c = dec(w)` satisfies `cfold_θ(c) = c'`, and `w = c` on the fibre over every `η ∈ Y`. -/
theorem cone_step {μ : ℕ} (hD : IsSmoothDomain D μ) (hμ : 1 ≤ μ) {d : ℕ} {δ : ℚ}
    (hδ : δ ≤ (1 - rate (sqDom D) d) / 2) (w : D → F)
    (θ : F) (hgood : CGood δ d w θ) (c' : sqDom D → F) (hc' : c' ∈ RS (sqDom D) d)
    (hY : (1 - δ) * Nat.card (sqDom D) ≤ (agreeSet (cwfold θ w) c').ncard) :
    FibDistLE w (RS D (2 * d) : Set (D → F)) δ ∧
    cwfold θ (dec (RS D (2 * d) : Set (D → F)) δ w) = c' ∧
    ∀ η ∈ agreeSet (cwfold θ w) c', ∀ ξ ∈ fibre η,
      w ξ = dec (RS D (2 * d) : Set (D → F)) δ w ξ := by
  haveI := hD.finite
  have hneg : (-1 : Fˣ) ∈ D := hD.neg_one_mem hμ
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_smooth hD hμ
  have hpos : (0 : ℚ) < Nat.card (sqDom D) := by
    have : Nonempty (sqDom D) := ⟨1⟩
    exact_mod_cast Nat.card_pos
  have hdist : relDist (cwfold θ w) c' ≤ δ := by
    have h := agree_add_hdist (cwfold θ w) c'
    have h' : ((agreeSet (cwfold θ w) c').ncard : ℚ) + hdist (cwfold θ w) c'
        = Nat.card (sqDom D) := by exact_mod_cast h
    unfold relDist
    rw [div_le_iff₀ hpos]
    linarith
  have hclose : FibDistLE w (RS D (2 * d) : Set (D → F)) δ := by
    by_contra hfar
    exact hgood.1 hfar ⟨c', hc', hdist⟩
  set c := dec (RS D (2 * d) : Set (D → F)) δ w
  obtain ⟨hcC, hcw⟩ := dec_spec hclose
  have hfc : cwfold θ c ∈ RS (sqDom D) d := cwfold_mem_RS hneg h2 θ hcC
  obtain ⟨S, hS, hSagree⟩ := (fibDist_le_iff w c δ).1 hcw
  have hagr1 : (1 - δ) * Nat.card (sqDom D) ≤ (agreeSet (cwfold θ c) (cwfold θ w)).ncard := by
    refine hS.trans ?_
    have : S ⊆ agreeSet (cwfold θ c) (cwfold θ w) := by
      intro η hη
      exact (cwfold_congr θ (hSagree η hη)).symm
    exact_mod_cast Set.ncard_le_ncard this (Set.toFinite _)
  have hagr := agree_trans_frac (cwfold θ c) (cwfold θ w) c' _ _ hagr1 hY
  have hrate : rate (sqDom D) d * Nat.card (sqDom D) = d := by
    rw [rate, div_mul_cancel₀ _ hpos.ne']
  have heq : cwfold θ c = c' := by
    by_contra hne
    have hlt := RS_agree_lt hfc hc' hne
    have hlt' : ((agreeSet (cwfold θ c) c').ncard : ℚ) < d := by exact_mod_cast hlt
    have : (d : ℚ) ≤ (1 - δ + (1 - δ) - 1) * Nat.card (sqDom D) := by
      rw [← hrate]
      have : rate (sqDom D) d ≤ 1 - δ + (1 - δ) - 1 := by linarith
      exact mul_le_mul_of_nonneg_right this hpos.le
    linarith
  refine ⟨hclose, heq, ?_⟩
  intro η hη ξ hξ
  by_contra hne
  apply hgood.2 hclose η ⟨ξ, hξ, hne⟩
  rw [show cwfold θ w η = c' η from hη, ← heq]

end Good

end SumFRI
