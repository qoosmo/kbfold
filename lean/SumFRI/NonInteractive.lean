/-
SumFRI/NonInteractive.lean
§6.7 of the Sum-FRI paper ("The non-interactive scheme"): the deterministic and combinatorial
content of the passage from Theorem 6.20 (round-by-round knowledge soundness) to relaxed
round-by-round knowledge soundness (Definition 3.13) of the IOR `Π_eval^Σ`.

The parts that do not involve the fold or the round checks are those of
`KBFold/NonInteractive.lean` and are reused: fibre strings `fib`, `unfib`, `relDist_fib`; partial
strings `fill`, `pDist`, `relDist_fill_le`, `pDist_le_iff`; Lemma 6.23 (sampling) `sampleF`,
`prob_sample_le`, `prob_sample_event_le`, `prob_equiv_sample`; `δstar`; the transcript data
`PTransE` (`y`, `word`, `w0`, `filled`, `updR`); the stages `Stage`; and `rrbr_trivial`.

This file proves, for the coefficient-form scheme:
* the relation `(R_eval)_{≤δ}`: `cRelE`, `cRelE_full_iff`;
* Lemma 6.28 (deterministic core): `ccr_unique_core`, `ccr_unique_eval`;
* witness sets with erasures `cWsetE`, `cdensE`, the doomed set `cNotDoomedE`/`cDoomedE`;
* Lemma 6.25: `crbr_stepE`, `crbr_escapeE`, `cdensE_zero_pDist`, `cEsig_eq_of_densE`,
  items (1)–(3) `crbr_erasures_one`, `crbr_erasures_round`, `crbr_erasures_final`;
* Definition 6.24 `cKState` and Theorem 6.26: `crrbr_round`, `crrbr_final`.
Outside Lean, as in KBFold: the Merkle-collision step of Lemma 6.28 and Corollary 6.27 (the
compiler of [CDHZ25]).
-/
import SumFRI.RBR
import KBFold.NonInteractive

set_option autoImplicit false

open Polynomial Finset

namespace SumFRI

open KBFold

variable {F : Type*} [Field F]

/-! ### Lemma 6.28 (deterministic core) -/

section CRUnique

variable {L : Subgroup Fˣ}

/-- **Lemma 6.28, deterministic core.**  Let `δ ≤ (1-ρ)/2` with `ρ = 2^n/M` the rate of
`𝒞₀ = RS[L, 2^n]`, and let the partial strings `y, y'` over `Σ = F × F` (indexed by `L₁`) satisfy
`Δ(y, fib₀(Enc f)) ≤ δ` and `Δ(y', fib₀(Enc f')) ≤ δ` (i.e. they agree with these strings on at
least `(1-δ)M/2` fibres, `pDist_le_iff`).  If `f ≠ f'`, then some position `η` is opened in both
(`y η ≠ ⊥ ≠ y' η`) to different values.  The remaining step of the paper — two accepting openings
of one position to different values under one root yield a collision of the random oracle
(salted form of Lemma KBFold Lemma 3.13) — concerns the hash function and is not formalised. -/
theorem ccr_unique_core [Finite L] (hD : (-1 : Fˣ) ∈ L) (h2 : (2 : F) ≠ 0) {n : ℕ}
    (hn : 2 ^ n ≤ Nat.card L) {δ : ℚ} (hδ : δ ≤ (1 - rate L (2 ^ n)) / 2)
    (y y' : sqDom L → Option (F × F)) (f f' : Table F n)
    (hy : pDist y (fib (cEnc L f)) ≤ δ) (hy' : pDist y' (fib (cEnc L f')) ≤ δ) (hne : f ≠ f') :
    ∃ η, y η ≠ none ∧ y' η ≠ none ∧ y η ≠ y' η := by
  haveI : Finite (sqDom L) := sqDom_finite
  haveI : Nonempty (sqDom L) := ⟨1⟩
  set K := Nat.card (sqDom L)
  have hM : Nat.card L = 2 * K := card_eq_two_mul_sqDom hD h2
  have hK : (0 : ℚ) < K := by exact_mod_cast Nat.card_pos
  set A := {η | y η = some (fib (cEnc L f) η)}
  set A' := {η | y' η = some (fib (cEnc L f') η)}
  have hA := (pDist_le_iff y _ δ).1 hy
  have hA' := (pDist_le_iff y' _ δ).1 hy'
  -- `|A ∩ A'| ≥ (1 - 2δ) M/2 ≥ ρ M/2 = 2^n/2`
  have hI : ((A ∩ A').ncard : ℚ) + (A ∪ A').ncard = A.ncard + A'.ncard := by
    exact_mod_cast Set.ncard_inter_add_ncard_union A A'
  have hU : ((A ∪ A').ncard : ℚ) ≤ K := by
    have := Set.ncard_le_ncard (Set.subset_univ (A ∪ A')) (Set.toFinite _)
    rw [Set.ncard_univ] at this; exact_mod_cast this
  have hrate : rate L (2 ^ n) * (2 * K) = 2 ^ n := by
    rw [rate, hM]; push_cast; field_simp
  have hAA : (2 ^ n : ℚ) ≤ 2 * (A ∩ A').ncard := by
    rw [← hrate]
    nlinarith
  by_contra hcon
  push_neg at hcon
  -- `Enc f` and `Enc f'` agree on the fibres over `A ∩ A'`
  have hsub : sqPt ⁻¹' (A ∩ A') ⊆ agreeSet (cEnc L f) (cEnc L f') := by
    intro ξ hξ
    obtain ⟨h1, h1'⟩ := hξ
    have hs : y (sqPt ξ) = y' (sqPt ξ) :=
      hcon _ (by rw [h1]; simp) (by rw [h1']; simp)
    have hfe : fib (cEnc L f) (sqPt ξ) = fib (cEnc L f') (sqPt ξ) := by
      have := h1.symm.trans (hs.trans h1')
      exact Option.some_injective _ this
    exact (fib_eq_iff hD _ _ _).1 hfe ξ rfl
  have hcard : 2 * (A ∩ A').ncard ≤ (agreeSet (cEnc L f) (cEnc L f')).ncard := by
    rw [← ncard_preimage_sqPt hD h2]
    exact Set.ncard_le_ncard hsub (Set.toFinite _)
  have hEq : cEnc L f = cEnc L f' := by
    by_contra hE
    have hlt := RS_agree_lt (cEnc_mem_RS L f) (cEnc_mem_RS L f') hE
    have : (2 ^ n : ℚ) < 2 ^ n := by
      calc (2 ^ n : ℚ) ≤ 2 * (A ∩ A').ncard := hAA
        _ ≤ (agreeSet (cEnc L f) (cEnc L f')).ncard := by exact_mod_cast hcard
        _ < 2 ^ n := by exact_mod_cast hlt
    exact lt_irrefl _ this
  exact hne (cEnc_injective hn hEq)

/-- **Lemma 6.28, last sentence:** if `z = z'` and `v ≠ v'`, then `f ≠ f'`, so
`ccr_unique_core` applies. -/
theorem ccr_unique_eval {n : ℕ} (f f' : Table F n) (z : Fin n → F) {v v' : F}
    (hv : cpoly f z = v) (hv' : cpoly f' z = v') (hne : v ≠ v') : f ≠ f' := by
  rintro rfl; exact hne (hv.symm.trans hv')

end CRUnique

/-! ### The relation `R_eval` -/

section Relation

variable {L : Subgroup Fˣ} {m : ℕ} (ℓ : ℕ) (zp : ℕ → F) (zs : Fin m → F) (v : F) (δ : ℚ)

/-- **§6.7, the relation:** `((z,v), y, f) ∈ (R_eval)_{≤δ}` iff `Δ(y, fib₀(Enc f)) ≤ δ` and
`P_f(z) = v`, for a partial string `y` over `Σ` indexed by `L₁` (`⊥` counts as a disagreement). -/
def cRelE (y : sqDom L → Option (F × F)) (f : Table F (m + ℓ)) : Prop :=
  pDist y (fib (cEnc L f)) ≤ δ ∧ cpoly f (catPt ℓ zp zs) = v

/-- **§6.7, the relation:** for a full string `y = fib₀(w₀)`, `(R_eval)_{≤δ}` is the relation
`R^δ_eval` of §6.6 (`cIsWitness`), by equation (`eq:fib-hamming`). -/
theorem cRelE_full_iff (hL : (-1 : Fˣ) ∈ L) (w0 : L → F) (f : Table F (m + ℓ)) :
    cRelE ℓ zp zs v δ (fun η => some (fib w0 η)) f ↔ cIsWitness ℓ w0 zp zs v δ f := by
  have : pDist (fun η => some (fib w0 η)) (fib (cEnc L f)) = relDist (fib w0) (fib (cEnc L f)) := by
    unfold pDist relDist hdist disagreeSet
    simp only [Ne, Option.some.injEq]
  rw [cRelE, cIsWitness, this, relDist_fib hL]

end Relation

/-! ### Witness sets with erasures and the doomed set `𝒟^⊥_δ` -/

section Erasures

variable {L : Subgroup Fˣ} {m : ℕ} (ℓ : ℕ) (zp : ℕ → F) (zs : Fin m → F) (v : F) (δ : ℚ)

/-- **§6.7, erasures:** `𝒲^⊥_j(c) = {ξ ∈ 𝒲_j(c) : ξ^{2^i} ∉ 𝒰_{i-1} for all i ∈ [1, max(j,1)]}`,
where `𝒰_{i-1}` is the set of erased positions of `U (i-1)` and `𝒲_j` is computed on the filled
words. -/
def cWsetE (τ : PTransE F L) (j : ℕ) (c : lv L j → F) : Set L :=
  {ξ | ξ ∈ cWset τ.w0 τ.filled j c ∧ ∀ i < max j 1, τ.U i (ptAt ξ (i + 1)) ≠ none}

/-- `cdens^⊥_j(c) = |𝒲^⊥_j(c)| / M`. -/
noncomputable def cdensE (τ : PTransE F L) (j : ℕ) (c : lv L j → F) : ℚ :=
  ((cWsetE τ j c).ncard : ℚ) / Nat.card L

/-- **§6.7, erasures:** `τ_j ∉ 𝒟^⊥_δ` (Definition 6.17 with `cdens^⊥_j` in place of `dens_j`). -/
def cNotDoomedE (τ : PTransE F L) (j : ℕ) : Prop :=
  RestrT zp v τ.filled j ∧ ∃ c ∈ RS (lv L j) (Nd m ℓ j),
    1 - δ ≤ cdensE τ j c ∧ vvT v τ.filled j = csigmaJ ℓ zp zs j c

/-- **§6.7, erasures:** `τ_j ∈ 𝒟^⊥_δ` (`τ_0` is always doomed). -/
def cDoomedE (τ : PTransE F L) (j : ℕ) : Prop := j = 0 ∨ ¬ cNotDoomedE ℓ zp zs v δ τ j

variable {ℓ zp zs v δ}

/-- §6.7, erasures: `𝒲^⊥_j(c) ⊆ 𝒲_j(c)`. -/
lemma cWsetE_subset (τ : PTransE F L) (j : ℕ) (c : lv L j → F) :
    cWsetE τ j c ⊆ cWset τ.w0 τ.filled j c := fun _ h => h.1

/-- §6.7, erasures: `cdens^⊥_j(c) ≤ dens_j(c)`. -/
lemma cdensE_le_dens [Finite L] (τ : PTransE F L) (j : ℕ) (c : lv L j → F) :
    cdensE τ j c ≤ cdens τ.w0 τ.filled j c :=
  div_le_div_of_nonneg_right
    (by exact_mod_cast (Set.ncard_le_ncard (cWsetE_subset τ j c) (Set.toFinite _)))
    (Nat.cast_nonneg _)

/-- **§6.7:** without erasures, `𝒲^⊥_j = 𝒲_j` (so `𝒟^⊥_δ` is the doomed set of Definition 6.17). -/
theorem cWsetE_eq_of_no_erasure (τ : PTransE F L) (h : ∀ i η, τ.U i η ≠ none) (j : ℕ)
    (c : lv L j → F) : cWsetE τ j c = cWset τ.w0 τ.filled j c := by
  ext ξ; exact ⟨fun hξ => hξ.1, fun hξ => ⟨hξ, fun i _ => h i _⟩⟩

/-- **§6.7:** without erasures, `τ_j ∉ 𝒟^⊥_δ` iff `τ_j` is not doomed in the sense of
Definition 6.17 (for the filled transcript). -/
theorem cNotDoomedE_iff_of_no_erasure (τ : PTransE F L) (h : ∀ i η, τ.U i η ≠ none) (j : ℕ) :
    cNotDoomedE ℓ zp zs v δ τ j ↔ cNotDoomed ℓ τ.w0 zp zs v δ τ.filled j := by
  simp only [cNotDoomedE, cNotDoomed, cdensE, cdens, cWsetE_eq_of_no_erasure τ h]

/-- `𝒲^⊥_j(c)` does not depend on the challenge `r_{j+1}`. -/
lemma cWsetE_updR (τ : PTransE F L) (j : ℕ) (a : F) (c : lv L j → F) :
    cWsetE (τ.updR j a) j c = cWsetE τ j c := by
  simp only [cWsetE, PTransE.filled_updR]
  rw [show (τ.updR j a).w0 = τ.w0 from rfl, cWset_updR]
  rfl

/-- `τ_j ∉ 𝒟^⊥_δ` does not depend on the challenge `r_{j+1}`. -/
theorem cNotDoomedE_updR (τ : PTransE F L) (j : ℕ) (a : F) :
    cNotDoomedE ℓ zp zs v δ (τ.updR j a) j ↔ cNotDoomedE ℓ zp zs v δ τ j := by
  simp only [cNotDoomedE, cdensE, cWsetE_updR, PTransE.filled_updR,
    vvT_updR τ.filled j a j le_rfl, RestrT]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i hi => ?_, h2⟩
    have := h1 i hi
    rwa [vvT_updR τ.filled j a i hi.le] at this
  · rintro ⟨h1, h2⟩
    refine ⟨fun i hi => ?_, h2⟩
    rw [vvT_updR τ.filled j a i hi.le]
    exact h1 i hi

end Erasures

/-! ### Lemma 6.25 -/

section Step

variable {L : Subgroup Fˣ} {m : ℕ} {ℓ : ℕ} {zp : ℕ → F} {zs : Fin m → F} {v : F} {δ : ℚ}

/-- **Lemma 6.25, first paragraph of the proof (Lemma 6.18 with `𝒲^⊥`).** Let
`j < ℓ` (the paper's round `j+1`) and `r_{j+1}` good for the filled word `w_j`.  If `c' ∈ 𝒞_{j+1}`
has `cdens^⊥_{j+1}(c') ≥ 1-δ`, then `Δ^fib_j(w_j, 𝒞_j) ≤ δ`, `c = dec_j(w_j)` satisfies
`fold_{r_{j+1}}(c) = c'`, and `𝒲^⊥_{j+1}(c') ⊆ 𝒲^⊥_j(c)`. -/
theorem crbr_stepE {R : ℕ} (hL : IsSmoothDomain L (m + ℓ + R)) (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2)
    (τ : PTransE F L) {j : ℕ} (hj : j < ℓ) (hgood : cGoodAt ℓ δ m j (τ.word j) (τ.r j))
    (c' : lv L (j + 1) → F) (hc' : c' ∈ RS (lv L (j + 1)) (Nd m ℓ (j + 1)))
    (hdens : 1 - δ ≤ cdensE τ (j + 1) c') :
    FibDistLE (τ.word j) (RS (lv L j) (2 * Nd m ℓ (j + 1)) : Set _) δ ∧
      cwfold (τ.r j) (cdecAt ℓ δ m j (τ.word j)) = c' ∧
      cWsetE τ (j + 1) c' ⊆ cWsetE τ j (cdecAt ℓ δ m j (τ.word j)) := by
  haveI := hL.finite
  have hd : 1 - δ ≤ cdens τ.w0 τ.filled (j + 1) c' := hdens.trans (cdensE_le_dens _ _ _)
  have hgood' : cGoodAt ℓ δ m j (Wd τ.w0 τ.filled j) (τ.filled.r j) := by
    rw [PTransE.Wd_filled]; exact hgood
  obtain ⟨hF, hfold, hsub⟩ := crbr_step hL hδ τ.filled hj hgood' c' hc' hd
  rw [PTransE.Wd_filled] at hF hfold hsub
  refine ⟨hF, hfold, fun ξ hξ => ⟨hsub hξ.1, fun i hi => hξ.2 i ?_⟩⟩
  have : max j 1 ≤ max (j + 1) 1 := max_le_max (by omega) le_rfl
  omega

/-- Core of the proof of Lemma 6.25 (1) and (2): if `r_{j+1} = a` is not bad and
`τ_{j+1} ∉ 𝒟^⊥_δ`, then `c = dec_j(w_j)` exists, the restriction checks `1..j` hold,
`cdens^⊥_j(c) ≥ 1-δ` and `v_j = σ_j(c)`. -/
theorem crbr_escapeE {R : ℕ} (hL : IsSmoothDomain L (m + ℓ + R)) (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2)
    (τ : PTransE F L) {j : ℕ} (hj : j < ℓ) (a : F)
    (hbad : ¬ cBadR ℓ τ.w0 zp zs δ τ.filled j a)
    (hnd : cNotDoomedE ℓ zp zs v δ (τ.updR j a) (j + 1)) :
    FibDistLE (τ.word j) (RS (lv L j) (2 * Nd m ℓ (j + 1)) : Set _) δ ∧
      RestrT zp v τ.filled j ∧ 1 - δ ≤ cdensE τ j (cdecAt ℓ δ m j (τ.word j)) ∧
      vvT v τ.filled j = csigmaJ ℓ zp zs j (cdecAt ℓ δ m j (τ.word j)) := by
  haveI := hL.finite
  obtain ⟨hSC, c', hc', hdE, hv⟩ := hnd
  have hnd' : cNotDoomed ℓ τ.w0 zp zs v δ (τ.filled.updR j a) (j + 1) :=
    ⟨hSC, c', hc', hdE.trans (cdensE_le_dens _ _ _), hv⟩
  obtain ⟨hF, hSC', -, hv'⟩ := crbr_escape hL hδ τ.filled hj a hbad hnd'
  rw [PTransE.Wd_filled] at hF hv'
  have hgood : cGoodAt ℓ δ m j ((τ.updR j a).word j) ((τ.updR j a).r j) := by
    have h := hbad
    simp only [cBadR, not_or, not_not] at h
    have e : (τ.updR j a).r j = a := by simp [PTransE.updR]
    rw [e]
    have h1 := h.1
    rw [PTransE.Wd_filled] at h1
    exact h1
  obtain ⟨-, -, hsub⟩ := crbr_stepE hL hδ (τ.updR j a) hj hgood c' hc' hdE
  have hsub' : cWsetE (τ.updR j a) (j + 1) c' ⊆ cWsetE τ j (cdecAt ℓ δ m j (τ.word j)) := by
    have := hsub
    rw [cWsetE_updR] at this
    exact this
  refine ⟨hF, hSC', hdE.trans ?_, hv'⟩
  exact div_le_div_of_nonneg_right
    (by exact_mod_cast Set.ncard_le_ncard hsub' (Set.toFinite _)) (Nat.cast_nonneg _)

end Step

section ItemOne

variable {L : Subgroup Fˣ} {m : ℕ} {ℓ : ℕ} {δ : ℚ}

/-- **Lemma 6.25, proof of (1), key deduction:** `𝒲^⊥_0(c)` consists of points
`ξ` with `ξ² ∉ 𝒰_0` and `w_0 = c` on `{±ξ}`, i.e. lies over the fibres `η` with
`y(η) = fib_0(c)(η)` (in particular `y(η) ≠ ⊥`); so `cdens^⊥_0(c) ≥ 1-δ` gives
`Δ(y, fib_0(c)) ≤ δ`.  (Only the inclusion, not the paper's equality "twice the number", is
needed.) -/
theorem cdensE_zero_pDist (hL0 : (-1 : Fˣ) ∈ L) (h2 : (2 : F) ≠ 0) [Finite L] (τ : PTransE F L)
    (c : L → F) (h : 1 - δ ≤ cdensE τ 0 c) :
    pDist τ.y (fib c) ≤ δ := by
  haveI : Finite (sqDom L) := sqDom_finite
  haveI : Nonempty (sqDom L) := ⟨1⟩
  haveI : Nonempty L := ⟨1⟩
  set A : Set (sqDom L) := {η | τ.y η = some (fib c η)}
  have hsub : cWsetE τ 0 c ⊆ sqPt ⁻¹' A := by
    intro ξ hξ
    obtain ⟨hW, hU⟩ := hξ
    have hU0 : τ.y (sqPt ξ) ≠ none := hU 0 (by simp)
    have hW' : τ.w0 ξ = c ξ ∧ τ.w0 (negPt ξ) = c (negPt ξ) := hW
    have hfib : fib τ.w0 (sqPt ξ) = fib c (sqPt ξ) := by
      refine (fib_eq_iff hL0 _ _ _).2 (fun ζ hζ => ?_)
      rw [fibre_sqPt hL0] at hζ
      rcases hζ with rfl | rfl
      · exact hW'.1
      · exact hW'.2
    have hfill : fib τ.w0 = fill τ.y :=
      fib_unfib (D := L) hL0 h2 _
    rw [hfill] at hfib
    show τ.y (sqPt ξ) = some (fib c (sqPt ξ))
    revert hU0 hfib
    simp only [fill]
    cases τ.y (sqPt ξ) with
    | none => intro h; exact absurd rfl h
    | some p => intro _ hp; simp only [Option.getD_some] at hp; rw [hp]
  have hcard : (cWsetE τ 0 c).ncard ≤ 2 * A.ncard := by
    rw [← ncard_preimage_sqPt hL0 h2]
    exact Set.ncard_le_ncard hsub (Set.toFinite _)
  have hM : Nat.card L = 2 * Nat.card (sqDom L) := card_eq_two_mul_sqDom hL0 h2
  have hpos : (0 : ℚ) < Nat.card L := by exact_mod_cast Nat.card_pos
  rw [pDist_le_iff]
  rw [cdensE, le_div_iff₀ hpos, hM] at h
  have hc : ((cWsetE τ 0 c).ncard : ℚ) ≤ 2 * A.ncard := by exact_mod_cast hcard
  push_cast at h
  linarith

variable (ℓ) in
/-- **Definition 6.24 (the algorithm `E`):** read `y`, let `w₀ = fib₀^{-1}(ȳ)`, and output
the decoded table of `w₀` at radius `δ*` if `Δ^fib₀(w₀, 𝒞₀) ≤ δ*`, and the zero table otherwise
(the extractor `cExt` of Definition 6.17 at radius `δ*`).  It depends only on `y = τ.U 0`, not
on `δ`. -/
noncomputable def cEsig (R : ℕ) (τ : PTransE F L) : Table F (m + ℓ) := cExt ℓ τ.w0 (δstar R)

/-- **Lemma 5.2 (encoding)**, inverse: a table is the table of kernel coordinates of its
encoding (used for `E(y) = λ[c]` in Lemma 6.25(1)). -/
lemma ccoeffs_polyOf_cEnc [Finite L] {n : ℕ} (hn : 2 ^ n ≤ Nat.card L) (f : Table F n) :
    ccoeffs n (polyOf (cEnc L f)) = f := by
  rw [cEnc, polyOf_ev (degreeLT_mono' hn (vpoly_mem_degreeLT f)), ccoeffs_vpoly]

/-- **Lemma 6.25, proof of (1):** if `c ∈ 𝒞₀` and `cdens^⊥_0(c) ≥ 1-δ` with
`δ ≤ δ*`, then `Δ^fib₀(w₀, c) = Δ(ȳ, fib₀(c)) ≤ Δ(y, fib₀(c)) ≤ δ ≤ δ*`, so decoding the filled
word at radius `δ*` gives `c`: `Enc(E(y)) = c`, i.e. `E(y) = λ[c]` (Lemmas 6.3 and 5.2). -/
theorem cEsig_eq_of_densE {R : ℕ} (hL : IsSmoothDomain L (m + ℓ + R)) (hℓR : 1 ≤ m + ℓ + R)
    (hδ : δ ≤ δstar R) (τ : PTransE F L) {c : L → F} (hc : c ∈ RS L (2 ^ (m + ℓ)))
    (h : 1 - δ ≤ cdensE τ 0 c) :
    cEnc L (cEsig (m := m) ℓ R τ) = c ∧ pDist τ.y (fib c) ≤ δ := by
  classical
  haveI := hL.finite
  have hL0 : (-1 : Fˣ) ∈ L := hL.neg_one_mem hℓR
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_smooth hL hℓR
  have hp := cdensE_zero_pDist hL0 h2 τ c h
  have hfd : fibDist τ.w0 c ≤ δ := by
    rw [← relDist_fib hL0]
    have hfill : fib τ.w0 = fill τ.y :=
      fib_unfib (D := L) hL0 h2 _
    rw [hfill]
    exact (relDist_fill_le _ _).trans hp
  have hfd' : fibDist τ.w0 c ≤ δstar R := hfd.trans hδ
  have hF : FibDistLE τ.w0 (RS L (2 ^ (m + ℓ)) : Set (L → F)) (δstar R) := ⟨c, hc, hfd'⟩
  have hn : 2 ^ (m + ℓ) ≤ Nat.card L := Nd_le_card (ℓ := ℓ) hL (j := 0) (by omega)
  have hrate : rate L (2 ^ (m + ℓ)) = 1 / 2 ^ R := rate_lv (ℓ := ℓ) hL (j := 0) (by omega)
  have hδ' : δstar R ≤ (1 - rate L (2 ^ (m + ℓ))) / 2 := by rw [hrate]; exact le_rfl
  have hE : cEsig ℓ R τ = cdecTable L (m + ℓ) (δstar R) τ.w0 := by simp [cEsig, cExt, hF]
  refine ⟨?_, hp⟩
  rw [hE, cdecTable_spec hn hF]
  exact dec_unique hL0 h2 hδ' hc hfd'

end ItemOne

section Items

variable {L : Subgroup Fˣ} {m : ℕ} {ℓ : ℕ} {zp : ℕ → F} {zs : Fin m → F} {v : F} {δ : ℚ}

/-- **Lemma 6.25 (1).** Let `0 < δ ≤ δ*` and `ℓ ≥ 1`.  If
`((z,v), y, E(y)) ∉ (R_eval)_{≤δ}`, then, for every round-1 message (`s_1 ∈ F[X]_{<2}`), at most
`M_1 + 1` values of `r_1` make `τ_1 ∉ 𝒟^⊥_δ`. -/
theorem crbr_erasures_one [Fintype F] [DecidableEq F] {R : ℕ} (hL : IsSmoothDomain L (m + ℓ + R))
    (hℓ : 1 ≤ ℓ) (hδ0 : 0 < δ) (hδ : δ ≤ δstar R) (τ : PTransE F L)
    (hnw : ¬ cRelE ℓ zp zs v δ τ.y (cEsig ℓ R τ))
    (hdeg : (τ.s 0).natDegree ≤ 1) :
    ({a : F | cNotDoomedE ℓ zp zs v δ (τ.updR 0 a) 1}.ncard : ℚ) ≤ Nat.card (lv L 1) + 1 := by
  classical
  haveI := hL.finite
  have hsub : {a : F | cNotDoomedE ℓ zp zs v δ (τ.updR 0 a) 1} ⊆
      {a : F | cBadR ℓ τ.w0 zp zs δ τ.filled 0 a} := by
    intro a hnd
    by_contra hbad
    obtain ⟨hF, -, hdens, hv⟩ := crbr_escapeE hL hδ τ (by omega) a hbad hnd
    set c := cdecAt ℓ δ m 0 (τ.word 0)
    have e0 : 2 * Nd m ℓ (0 + 1) = 2 ^ (m + ℓ) := by rw [Nd_succ (by omega)]; rfl
    have hc : c ∈ RS L (2 ^ (m + ℓ)) := by
      have h1 : c ∈ RS (lv L 0) (2 * Nd m ℓ (0 + 1)) := (dec_spec hF).1
      have e : RS (lv L 0) (2 * Nd m ℓ (0 + 1)) = RS L (2 ^ (m + ℓ)) := by rw [e0]; rfl
      rw [e] at h1; exact h1
    obtain ⟨hEnc, hp⟩ := cEsig_eq_of_densE hL (by omega) hδ τ hc hdens
    apply hnw
    refine ⟨by rw [hEnc]; exact hp, ?_⟩
    have hn : 2 ^ (m + ℓ) ≤ Nat.card L := Nd_le_card (ℓ := ℓ) hL (j := 0) (by omega)
    rw [← ccoeffs_polyOf_cEnc hn (cEsig ℓ R τ), hEnc]
    have hv' : v = csigmaJ ℓ zp zs 0 c := hv
    rw [hv', csigmaJ]
    refine cpoly_ccoeffs_congr _ rfl _ _ (fun i => ?_)
    rw [catPt_eq_zfull]
    simp
  calc ({a : F | cNotDoomedE ℓ zp zs v δ (τ.updR 0 a) 1}.ncard : ℚ)
      ≤ {a : F | cBadR ℓ τ.w0 zp zs δ τ.filled 0 a}.ncard := by
        exact_mod_cast Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ Nat.card (lv L (0 + 1)) + 1 := card_cBadR hL hδ0 hδ τ.filled (by omega) hdeg

/-- **Lemma 6.25 (2).** Let `0 < δ ≤ δ*` and `1 ≤ j < ℓ` (the paper's round
`j+1 ∈ [2, ℓ]`).  If `τ_j ∈ 𝒟^⊥_δ`, then for every round-`(j+1)` message (partial strings, with
`s_{j+1} ∈ F[X]_{<2}`), at most `M_{j+1} + 1` values of `r_{j+1}` make `τ_{j+1} ∉ 𝒟^⊥_δ`. -/
theorem crbr_erasures_round [Fintype F] [DecidableEq F] {R : ℕ}
    (hL : IsSmoothDomain L (m + ℓ + R)) (hδ0 : 0 < δ) (hδ : δ ≤ δstar R) (τ : PTransE F L)
    {j : ℕ} (hj1 : 1 ≤ j) (hj : j < ℓ) (hdoom : cDoomedE ℓ zp zs v δ τ j)
    (hdeg : (τ.s j).natDegree ≤ 1) :
    ({a : F | cNotDoomedE ℓ zp zs v δ (τ.updR j a) (j + 1)}.ncard : ℚ) ≤
      Nat.card (lv L (j + 1)) + 1 := by
  classical
  have hnd : ¬ cNotDoomedE ℓ zp zs v δ τ j := by
    rcases hdoom with h | h
    · omega
    · exact h
  have hsub : {a : F | cNotDoomedE ℓ zp zs v δ (τ.updR j a) (j + 1)} ⊆
      {a : F | cBadR ℓ τ.w0 zp zs δ τ.filled j a} := by
    intro a hnd'
    by_contra hbad
    obtain ⟨hF, hSC, hdens, hv⟩ := crbr_escapeE hL hδ τ hj a hbad hnd'
    apply hnd
    have hmem := (dec_spec hF).1
    change cdecAt ℓ δ m j (τ.word j) ∈ (RS (lv L j) (2 * Nd m ℓ (j + 1)) : Set _) at hmem
    generalize cdecAt ℓ δ m j (τ.word j) = cs at hmem hdens hv
    rw [Nd_succ (by omega)] at hmem
    exact ⟨hSC, cs, hmem, hdens, hv⟩
  calc ({a : F | cNotDoomedE ℓ zp zs v δ (τ.updR j a) (j + 1)}.ncard : ℚ)
      ≤ {a : F | cBadR ℓ τ.w0 zp zs δ τ.filled j a}.ncard := by
        exact_mod_cast Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ Nat.card (lv L (j + 1)) + 1 := card_cBadR hL hδ0 hδ τ.filled hj hdeg

variable (ℓ zp zs v) in
/-- **§6.7, the verifier of `Π_eval^Σ`:** it rejects if an entry that it reads is `⊥` — the
restriction symbols and the final table (whose absence of `⊥` is the proposition `symOK`), and, for
each query point `ξ` and level `i+1 ∈ [1, ℓ]`, the entry at `ξ^{2^{i+1}}` of `U i` — and otherwise
runs the verifier of `Π_eval` on the filled words. -/
def cAcceptsSig (symOK : Prop) (τ : PTransE F L) (g : Table F m) {κ : ℕ} (ξ : Fin κ → L) : Prop :=
  symOK ∧ (∀ t, ∀ i < ℓ, τ.U i (ptAt (ξ t) (i + 1)) ≠ none) ∧
    cFullAccepts ℓ τ.w0 zp zs v τ.filled g ξ

/-- **Lemma 6.25 (3).** Let `δ ≤ δ*` and `ℓ ≥ 1`.  If `τ_ℓ ∈ 𝒟^⊥_δ`, then for every
final message `g`, the verifier of `Π_eval^Σ` accepts with probability at most `(1-δ)^κ` over the
query points. -/
theorem crbr_erasures_final [Fintype L] {R : ℕ} (hL : IsSmoothDomain L (m + ℓ + R)) (hℓ : 1 ≤ ℓ)
    (hδ : δ ≤ δstar R) (symOK : Prop) (τ : PTransE F L) (hdoom : cDoomedE ℓ zp zs v δ τ ℓ)
    (g : Table F m) (κ : ℕ) :
    prob (fun ξ : Fin κ → L => cAcceptsSig ℓ zp zs v symOK τ g ξ) ≤ (1 - δ) ^ κ := by
  classical
  have hR : (0 : ℚ) < 1 / 2 ^ R := by positivity
  have hδ1 : (0 : ℚ) ≤ 1 - δ := by unfold δstar at hδ; linarith
  have hnd : ¬ cNotDoomedE ℓ zp zs v δ τ ℓ := by
    rcases hdoom with h | h
    · omega
    · exact h
  haveI := hL.finite
  haveI : Nonempty L := ⟨1⟩
  haveI := lv_finite (L := L) ℓ
  set Pτ := cproverOf τ.filled g
  set wl := ev (lv L ℓ) (vpoly g)
  have hW : ∀ i < ℓ, Pτ.W ℓ τ.w0 τ.filled.r i = Wd τ.w0 τ.filled i := by
    intro i hi
    cases i with
    | zero => rfl
    | succ k => simp only [SumProver.W, if_neg (show k + 1 ≠ ℓ by omega)]; rfl
  have hWl : Pτ.W ℓ τ.w0 τ.filled.r ℓ = wl := cW_last Pτ τ.w0 hℓ τ.filled.r
  have hvv : ∀ i, Pτ.vv v τ.filled.r i = vvT v τ.filled i := by intro i; cases i <;> rfl
  by_cases hSC : RestrT zp v τ.filled ℓ ∧ Pτ.ClosureOK ℓ zs v τ.filled.r
  · obtain ⟨hSC, hCl⟩ := hSC
    have hd : 2 ^ m ≤ Nat.card (lv L ℓ) := by
      rw [← Nd_last (ℓ := ℓ)]; exact Nd_le_card hL (by omega)
    have hpoly : polyOf wl = vpoly g :=
      polyOf_ev (degreeLT_mono' hd (vpoly_mem_degreeLT g))
    have hσ : vvT v τ.filled ℓ = csigmaJ ℓ zp zs ℓ wl := by
      rw [← hvv, hCl, csigmaJ, hpoly,
        cpoly_ccoeffs_congr (vpoly g) (show m + ℓ - ℓ = m by omega)
          (fun i => zfull ℓ zp zs (ℓ + i)) zs (fun i => by rw [← zfull_ge zp zs i]; rfl),
        ccoeffs_vpoly]
      rfl
    have hwl : wl ∈ RS (lv L ℓ) (Nd m ℓ ℓ) := by
      rw [Nd_last]; exact ev_mem_RS (vpoly_mem_degreeLT g)
    have hdens : cdensE τ ℓ wl < 1 - δ := by
      by_contra hge
      push_neg at hge
      exact hnd ⟨hSC, wl, hwl, hge, hσ⟩
    -- a query point that passes its checks and reads no `⊥` lies in `𝒲^⊥_ℓ(w_ℓ)`
    have hq : ∀ ξ : L, Pτ.QueryOK ℓ τ.w0 τ.filled.r ξ →
        (∀ i < ℓ, τ.U i (ptAt ξ (i + 1)) ≠ none) → ξ ∈ cWsetE τ ℓ wl := by
      intro ξ hξ hU
      refine ⟨?_, fun i hi => hU i (by omega)⟩
      obtain ⟨k, rfl⟩ : ∃ k, ℓ = k + 1 := ⟨ℓ - 1, by omega⟩
      refine ⟨fun i hi => ?_, ?_⟩
      · have := hξ.1 i (by omega)
        simp only [SumProver.Chk] at this
        rw [hW i (by omega), hW (i + 1) (by omega)] at this
        exact this
      · have := hξ.1 k (by omega)
        simp only [SumProver.Chk] at this
        rw [hW k (by omega), hWl] at this
        exact this
    calc prob (fun ξ : Fin κ → L => cAcceptsSig ℓ zp zs v symOK τ g ξ)
        ≤ prob (fun ξ : Fin κ → L => ∀ t, ξ t ∈ (Set.toFinite (cWsetE τ ℓ wl)).toFinset) := by
          apply prob_mono
          intro ξ hacc t
          rw [Set.Finite.mem_toFinset]
          exact hq _ (hacc.2.2.2.2 t) (hacc.2.1 t)
      _ = (((Set.toFinite (cWsetE τ ℓ wl)).toFinset.card : ℚ) / Fintype.card L) ^ κ :=
          prob_forall_mem κ _
      _ ≤ (1 - δ) ^ κ := by
          apply pow_le_pow_left₀ (by positivity)
          rw [← Set.ncard_eq_toFinset_card, ← Nat.card_eq_fintype_card]
          exact hdens.le
  · have : ∀ ξ : Fin κ → L, ¬ cAcceptsSig ℓ zp zs v symOK τ g ξ := by
      intro ξ hacc
      apply hSC
      refine ⟨fun i hi => ?_, hacc.2.2.2.1⟩
      have := hacc.2.2.1 i hi
      rwa [hvv] at this
    calc prob (fun ξ : Fin κ → L => cAcceptsSig ℓ zp zs v symOK τ g ξ)
        = prob (fun _ : Fin κ → L => False) := by
          congr 1; funext ξ; simp only [this ξ]
      _ = 0 := prob_false
      _ ≤ (1 - δ) ^ κ := pow_nonneg hδ1 κ

end Items

/-! ### Definition 6.24 and Theorem 6.26 -/

section cKState

variable {L : Subgroup Fˣ} {m κ : ℕ} (ℓ : ℕ) (zp : ℕ → F) (zs : Fin m → F) (v : F) (R : ℕ)
  (symOK : Prop) (δ : ℚ)

/-- **Definition 6.24 (knowledge state function of `Π_eval^Σ`)**, for the statement
`((z,v), y)` with `y = τ.U 0`, the transcript data `τ`, and a table `f`:
1. on `tr_∅`: `((z,v), y, f) ∈ (R_eval)_{≤δ}`;
2. on a full transcript: the verifier of `Π_eval^Σ` accepts;
3. on `τ_j`, `j ∈ [1, ℓ]`: `τ_j ∉ 𝒟^⊥_δ` when `δ ∈ (0, δ*]`, and true otherwise;
4. a transcript ending with a prover message: by the stage indexing. -/
def cKState (τ : PTransE F L) (f : Table F (m + ℓ)) : Stage F L m κ → Prop
  | .empty => cRelE ℓ zp zs v δ τ.y f
  | .mid j => 0 < δ ∧ δ ≤ δstar R → cNotDoomedE ℓ zp zs v δ τ j
  | .full g ξ => cAcceptsSig ℓ zp zs v symOK τ g ξ

/-- **Definition 3.13, condition 1 (empty transcript)** for `cKState`. -/
theorem cKState_empty (τ : PTransE F L) (f : Table F (m + ℓ)) :
    cKState (κ := κ) ℓ zp zs v R symOK δ τ f .empty ↔
      cRelE ℓ zp zs v δ τ.y f := Iff.rfl

/-- **Definition 3.13, condition 3 (full transcript)** for `cKState`. -/
theorem cKState_full (τ : PTransE F L) (f : Table F (m + ℓ)) (g : Table F m) (ξ : Fin κ → L) :
    cKState ℓ zp zs v R symOK δ τ f (.full g ξ) ↔ cAcceptsSig ℓ zp zs v symOK τ g ξ := Iff.rfl

/-- `cKState` on `τ_j` does not depend on the table, nor on the challenge `r_{j+1}` (so it is a
function of the partial transcript `τ_j`). -/
theorem cKState_updR (τ : PTransE F L) (f f' : Table F (m + ℓ)) (j : ℕ) (a : F) :
    cKState (κ := κ) ℓ zp zs v R symOK δ (τ.updR j a) f (.mid j) ↔
      cKState (κ := κ) ℓ zp zs v R symOK δ τ f' (.mid j) := by
  simp only [cKState, cNotDoomedE_updR]

end cKState

section RRBR

variable {L : Subgroup Fˣ} {m : ℕ} {ℓ : ℕ} {zp : ℕ → F} {zs : Fin m → F} {v : F} {δ : ℚ}

/-- **Theorem 6.26, rounds `j+1 ∈ [1, ℓ]`.**  Let `δ ∈ (0, δ*]`, `num : [0,|F|-1] ≃ F`, and
`int : {0,1}^β ≃ [0, 2^β-1]`.  For every statement and transcript `tr = τ_j ‖ Π_{j+1}` (the data
`τ`; its challenge `r_{j+1}` is replaced by `φ(vr)`), with `s_{j+1} ∈ F[X]_{<2}`,
`Pr_{vr ← {0,1}^β}[∃ f, cKState(tr, E(y)) = 0 ∧ cKState(tr ‖ vr, f) = 1]
  ≤ (M_{j+1} + 1)(1/|F| + 2^{-β})`. -/
theorem crrbr_round [Fintype F] [DecidableEq F] {R : ℕ} (hL : IsSmoothDomain L (m + ℓ + R))
    (hδ0 : 0 < δ) (hδ : δ ≤ δstar R) (symOK : Prop) (κ : ℕ)
    (num : Fin (Fintype.card F) ≃ F) {β : ℕ} (int : (Fin β → Bool) ≃ Fin (2 ^ β))
    (τ : PTransE F L) {j : ℕ} (hj : j < ℓ) (hdeg : (τ.s j).natDegree ≤ 1) :
    prob (fun vr : Fin β → Bool => ∃ f : Table F (m + ℓ),
        ¬ cKState (κ := κ) ℓ zp zs v R symOK δ τ (cEsig ℓ R τ) (Stage.before j) ∧
        cKState (κ := κ) ℓ zp zs v R symOK δ (τ.updR j (sampleF num (int vr))) f
          (.mid (j + 1))) ≤
      ((Nat.card (lv L (j + 1)) : ℚ) + 1) * (1 / Fintype.card F + 1 / 2 ^ β) := by
  classical
  have hε : (0 : ℚ) ≤ 1 / Fintype.card F + 1 / 2 ^ β := by positivity
  by_cases h0 : cKState (κ := κ) ℓ zp zs v R symOK δ τ (cEsig ℓ R τ) (Stage.before j)
  · calc prob (fun vr : Fin β → Bool => ∃ f : Table F (m + ℓ),
            ¬ cKState (κ := κ) ℓ zp zs v R symOK δ τ (cEsig ℓ R τ) (Stage.before j) ∧
            cKState (κ := κ) ℓ zp zs v R symOK δ (τ.updR j (sampleF num (int vr))) f
              (.mid (j + 1)))
          = prob (fun _ : Fin β → Bool => False) := by
            congr 1; funext vr; simp only [h0, not_true_eq_false, false_and, exists_false]
        _ = 0 := prob_false
        _ ≤ _ := by positivity
  · have hcount : ({a : F | cNotDoomedE ℓ zp zs v δ (τ.updR j a) (j + 1)}.ncard : ℚ) ≤
        Nat.card (lv L (j + 1)) + 1 := by
      cases j with
      | zero =>
        exact crbr_erasures_one hL (by omega) hδ0 hδ τ h0 hdeg
      | succ k =>
        have hnd : ¬ cNotDoomedE ℓ zp zs v δ τ (k + 1) := fun h => h0 (fun _ => h)
        exact crbr_erasures_round hL hδ0 hδ τ (by omega) hj (Or.inr hnd) hdeg
    calc prob (fun vr : Fin β → Bool => ∃ f : Table F (m + ℓ),
            ¬ cKState (κ := κ) ℓ zp zs v R symOK δ τ (cEsig ℓ R τ) (Stage.before j) ∧
            cKState (κ := κ) ℓ zp zs v R symOK δ (τ.updR j (sampleF num (int vr))) f
              (.mid (j + 1)))
          ≤ prob (fun vr : Fin β → Bool =>
              cNotDoomedE ℓ zp zs v δ (τ.updR j (sampleF num (int vr))) (j + 1)) := by
            apply prob_mono
            rintro vr ⟨f, -, hK⟩
            exact hK ⟨hδ0, hδ⟩
        _ ≤ ({a : F | cNotDoomedE ℓ zp zs v δ (τ.updR j a) (j + 1)}.ncard : ℚ) *
              (1 / Fintype.card F + 1 / 2 ^ β) :=
            prob_sample_event_le num int (fun a => cNotDoomedE ℓ zp zs v δ (τ.updR j a) (j + 1))
        _ ≤ _ := mul_le_mul_of_nonneg_right hcount hε

/-- **Theorem 6.26, round `ℓ+1`.**  Let `δ ∈ (0, δ*]` and `ℓ ≥ 1`, and let the query
challenge range over a finite type `Ω` with a bijection `pos : Ω ≃ L^κ` (`{0,1}^{κ(n+R)}` in the
paper).  For every statement and transcript `τ_ℓ ‖ g`,
`Pr_{vr ← Ω}[∃ f, cKState(τ_ℓ, E(y)) = 0 ∧ cKState(τ_ℓ ‖ g ‖ vr, f) = 1] ≤ (1-δ)^κ`. -/
theorem crrbr_final [Fintype L] {R : ℕ} (hL : IsSmoothDomain L (m + ℓ + R)) (hℓ : 1 ≤ ℓ)
    (hδ0 : 0 < δ) (hδ : δ ≤ δstar R) (symOK : Prop) {κ : ℕ} {Ω : Type*} [Fintype Ω]
    (pos : Ω ≃ (Fin κ → L)) (τ : PTransE F L) (g : Table F m) :
    prob (fun ω : Ω => ∃ f : Table F (m + ℓ),
        ¬ cKState (κ := κ) ℓ zp zs v R symOK δ τ (cEsig ℓ R τ) (.mid ℓ) ∧
        cKState ℓ zp zs v R symOK δ τ f (.full g (pos ω))) ≤ (1 - δ) ^ κ := by
  classical
  have hR : (0 : ℚ) < 1 / 2 ^ R := by positivity
  have hδ1 : (0 : ℚ) ≤ 1 - δ := by unfold δstar at hδ; linarith
  by_cases h0 : cKState (κ := κ) ℓ zp zs v R symOK δ τ (cEsig ℓ R τ) (.mid ℓ)
  · calc prob (fun ω : Ω => ∃ f : Table F (m + ℓ),
            ¬ cKState (κ := κ) ℓ zp zs v R symOK δ τ (cEsig ℓ R τ) (.mid ℓ) ∧
            cKState ℓ zp zs v R symOK δ τ f (.full g (pos ω)))
          = prob (fun _ : Ω => False) := by
            congr 1; funext ω; simp only [h0, not_true_eq_false, false_and, exists_false]
        _ = 0 := prob_false
        _ ≤ _ := pow_nonneg hδ1 κ
  · have hdoom : cDoomedE ℓ zp zs v δ τ ℓ := Or.inr (fun h => h0 (fun _ => h))
    calc prob (fun ω : Ω => ∃ f : Table F (m + ℓ),
            ¬ cKState (κ := κ) ℓ zp zs v R symOK δ τ (cEsig ℓ R τ) (.mid ℓ) ∧
            cKState ℓ zp zs v R symOK δ τ f (.full g (pos ω)))
          ≤ prob (fun ω : Ω => cAcceptsSig ℓ zp zs v symOK τ g (pos ω)) := by
            apply prob_mono
            rintro ω ⟨f, -, hK⟩
            exact hK
        _ = prob (fun ξ : Fin κ → L => cAcceptsSig ℓ zp zs v symOK τ g ξ) :=
            prob_equiv_sample pos (fun ξ => cAcceptsSig ℓ zp zs v symOK τ g ξ)
        _ ≤ (1 - δ) ^ κ := crbr_erasures_final hL hℓ hδ symOK τ hdoom g κ

end RRBR

end SumFRI
