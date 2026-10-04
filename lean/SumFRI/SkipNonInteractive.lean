/-
SumFRI/SkipNonInteractive.lean
Theorem 6.32(3): relaxed round-by-round knowledge soundness of the IOR with committed levels `J`,
in the stage model of `SumFRI/NonInteractive.lean`.

Modelling.  A committed coset word of `Π_eval^{J,Σ}` is represented by its fibre string (the
unpacking of a coset symbol into its fibre symbols is a bijection, an erased coset giving erased
fibres); for an omitted level `j ∉ J`, the string `τ.U j` is not read.  The augmentation
`aug^Σ` of §6.8 inserts at an omitted level the full fibre string of the classical fold of the
preceding (filled) augmented word (`augU`, `augE`).  The knowledge state function of
`Π_eval^{J,Σ}` is that of `Π_eval^Σ` on the augmented transcript for partial transcripts, and
acceptance by the verifier of `Π_eval^{J,Σ}` (`cAcceptsSigJ`) on full ones.

* `cNotDoomedE_congr`: the doomed set `𝒟^⊥_δ` at stage `j` reads the strings `U_i` for
  `i < max j 1` only;
* `augU_updR`: the inserted strings up to level `j` do not depend on `θ_{j+1}`;
* `cAcceptsSigJ_aug`: acceptance by the verifier of `Π_eval^{J,Σ}` implies acceptance of the
  augmented transcript by the verifier of `Π_eval^Σ`;
* `crrbr_round_J`, `crrbr_final_J`: the bounds of Theorem 6.26 for `Π_eval^{J,Σ}`.
-/
import SumFRI.NonInteractive
import SumFRI.SkipRBR

set_option autoImplicit false

open Polynomial

namespace SumFRI

open KBFold

variable {F : Type*} [Field F]

/-! ### Congruence of the doomed set with erasures -/

/-- The witness set `𝒲_j(c)` reads `θ_i` and the words `w_i` for `i < j` only. -/
lemma cWset_congr {L : Subgroup Fˣ} (w0 : L → F) {τ τ' : PTrans F L} {j : ℕ}
    (h : ∀ i < j, τ.r i = τ'.r i ∧ Wd w0 τ i = Wd w0 τ' i) (c : lv L j → F) :
    cWset w0 τ j c = cWset w0 τ' j c := by
  cases j with
  | zero => rfl
  | succ k =>
    have hwhat : ∀ i < k + 1, cwhat w0 τ i = cwhat w0 τ' i := by
      intro i hi
      simp only [cwhat, (h i hi).1, (h i hi).2]
    ext ξ
    simp only [cWset, Set.mem_setOf_eq]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun i hi => ?_, ?_⟩
      · rw [← hwhat i (by omega), ← (h (i + 1) (by omega)).2]; exact h1 i hi
      · rw [← hwhat k (by omega)]; exact h2
    · rintro ⟨h1, h2⟩
      refine ⟨fun i hi => ?_, ?_⟩
      · rw [hwhat i (by omega), (h (i + 1) (by omega)).2]; exact h1 i hi
      · rw [hwhat k (by omega)]; exact h2

/-- `τ_j ∉ 𝒟^⊥_δ` reads the round polynomials, the challenges, and the strings `U_i` for
`i < max j 1` only. -/
theorem cNotDoomedE_congr {L : Subgroup Fˣ} {m ℓ : ℕ} {zp : ℕ → F} {zs : Fin m → F} {v : F}
    {δ : ℚ} {τ τ' : PTransE F L} {j : ℕ} (hs : τ.s = τ'.s) (hr : τ.r = τ'.r)
    (hU : ∀ i < max j 1, τ.U i = τ'.U i) :
    cNotDoomedE ℓ zp zs v δ τ j ↔ cNotDoomedE ℓ zp zs v δ τ' j := by
  have hw : ∀ i < max j 1, τ.word i = τ'.word i := by
    intro i hi
    unfold PTransE.word
    rw [hU i hi]
  have hw0 : τ.w0 = τ'.w0 := hw 0 (by omega)
  have hfs : ∀ i, τ.filled.s i = τ'.filled.s i := fun i => congrFun hs i
  have hfr : τ.filled.r = τ'.filled.r := hr
  have hvv : ∀ i, vvT v τ.filled i = vvT v τ'.filled i := by
    intro i
    cases i with
    | zero => rfl
    | succ i =>
      show (τ.filled.s i).eval (τ.filled.r i) = (τ'.filled.s i).eval (τ'.filled.r i)
      rw [hfs i, hfr]
  have hWset : ∀ c, cWset τ.w0 τ.filled j c = cWset τ'.w0 τ'.filled j c := by
    intro c
    rw [hw0]
    apply cWset_congr
    intro i hi
    refine ⟨by rw [hfr], ?_⟩
    cases i with
    | zero => rfl
    | succ i => exact hw (i + 1) (by omega)
  have hWsetE : ∀ c, cWsetE τ j c = cWsetE τ' j c := by
    intro c
    ext ξ
    simp only [cWsetE, Set.mem_setOf_eq, hWset c]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun i hi => by rw [← hU i hi]; exact h2 i hi⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun i hi => by rw [hU i hi]; exact h2 i hi⟩
  have hdens : ∀ c, cdensE τ j c = cdensE τ' j c := by
    intro c; simp only [cdensE, hWsetE c]
  simp only [cNotDoomedE, hdens, RestrT, hvv, hfs]

/-! ### The augmentation `aug^Σ` -/

section Aug

variable {L : Subgroup Fˣ}

/-- The augmented strings: `U_0 = y`; the string of a committed level; and, at an omitted level
`k+1 ∉ J`, the full fibre string of `cfold_{θ_{k+1}}` of the preceding filled augmented word. -/
noncomputable def augU (J : Finset ℕ) (τ : PTransE F L) : (i : ℕ) → lv L (i + 1) → Option (F × F)
  | 0 => τ.U 0
  | k + 1 =>
      if k + 1 ∈ J then τ.U (k + 1)
      else fun η =>
        some (fib (D := lv L (k + 1)) (cwfold (τ.r k) (unfib (D := lv L k) (fill (augU J τ k)))) η)

/-- The augmented transcript. -/
noncomputable def augE (J : Finset ℕ) (τ : PTransE F L) : PTransE F L := ⟨τ.s, augU J τ, τ.r⟩

/-- The inserted strings up to level `j` do not depend on the challenge `θ_{j+1}`. -/
lemma augU_updR (J : Finset ℕ) (τ : PTransE F L) (j : ℕ) (a : F) :
    ∀ i ≤ j, augU J (τ.updR j a) i = augU J τ i
  | 0, _ => rfl
  | k + 1, hk => by
      have ih := augU_updR J τ j a k (by omega)
      have hr : (τ.updR j a).r k = τ.r k := by
        simp only [PTransE.updR, Function.update_of_ne (show k ≠ j by omega)]
      have hU : ∀ i, (τ.updR j a).U i = τ.U i := fun _ => rfl
      simp only [augU, ih, hr, hU]

/-- `aug^Σ(τ_{j+1})` and `aug^Σ(τ_j)` with the challenge `θ_{j+1}` have the same doomed status at
stage `j+1`. -/
theorem cNotDoomedE_augE_updR {m ℓ : ℕ} {zp : ℕ → F} {zs : Fin m → F} {v : F} {δ : ℚ}
    (J : Finset ℕ) (τ : PTransE F L) (j : ℕ) (a : F) :
    cNotDoomedE ℓ zp zs v δ (augE J (τ.updR j a)) (j + 1) ↔
      cNotDoomedE ℓ zp zs v δ ((augE J τ).updR j a) (j + 1) :=
  cNotDoomedE_congr rfl rfl (fun i hi => augU_updR J τ j a i (by omega))

/-- The augmented words of Lemma 5.6 computed from the filled transcript are the filled
augmented words. -/
lemma augW_eq_augEword {m ℓ : ℕ} (J : Finset ℕ) (hneg : ∀ i < ℓ, (-1 : Fˣ) ∈ lv L i)
    (τ : PTransE F L) (g : Table F m) :
    ∀ j < ℓ, (cproverOf τ.filled g).augW ℓ J τ.w0 τ.r j = (augE J τ).word j
  | 0, _ => rfl
  | k + 1, hk => by
      have ih := augW_eq_augEword J hneg τ g k (by omega)
      simp only [SumProver.augW, if_neg (show k + 1 ≠ ℓ by omega)]
      by_cases hJ : k + 1 ∈ J
      · rw [if_pos hJ]
        show τ.word (k + 1) = unfib (D := lv L (k + 1)) (fill (augU J τ (k + 1)))
        simp only [augU, if_pos hJ, PTransE.word]
      · rw [if_neg hJ, ih]
        show cwfold (τ.r k) ((augE J τ).word k) =
          unfib (D := lv L (k + 1)) (fill (augU J τ (k + 1)))
        simp only [augU, if_neg hJ]
        exact (unfib_fib (hneg (k + 1) hk) _).symm

/-- The verifier words of the augmented prover are those of the augmented transcript. -/
lemma W_aug_eq_augE {m ℓ : ℕ} (J : Finset ℕ) (hneg : ∀ i < ℓ, (-1 : Fˣ) ∈ lv L i)
    (τ : PTransE F L) (g : Table F m) :
    ∀ j ≤ ℓ, ((cproverOf τ.filled g).aug ℓ J τ.w0).W ℓ τ.w0 τ.r j =
      (cproverOf (augE J τ).filled g).W ℓ τ.w0 τ.r j := by
  intro j hj
  rw [SumProver.aug_W_eq _ ℓ J τ.w0 τ.r j hj]
  rcases j with _ | k
  · rfl
  · by_cases h : k + 1 = ℓ
    · subst h
      simp [SumProver.augW, SumProver.W, cproverOf]
    · rw [augW_eq_augEword J hneg τ g (k + 1) (by omega)]
      simp only [SumProver.W, if_neg h]
      rfl

end Aug

/-! ### The verifier of `Π_eval^{J,Σ}` and Theorem 6.32(3) -/

section Theorem

variable {L : Subgroup Fˣ} {m : ℕ}

/-- The verifier of `Π_eval^{J,Σ}`: it rejects if a string entry that it reads at level `0` or
at a committed level is `⊥`, or if a round symbol or the final table is erased (`symOK`), and
otherwise runs the verifier of `Π_eval^J` on the filled words. -/
def cAcceptsSigJ (ℓ : ℕ) (J : Finset ℕ) (zp : ℕ → F) (zs : Fin m → F) (v : F) (symOK : Prop)
    (τ : PTransE F L) (g : Table F m) {κ : ℕ} (ξ : Fin κ → L) : Prop :=
  symOK ∧ (∀ t, ∀ i < ℓ, (i = 0 ∨ i ∈ J) → τ.U i (ptAt (ξ t) (i + 1)) ≠ none) ∧
    (cproverOf τ.filled g).AcceptsJ ℓ J τ.w0 zp zs v τ.r ξ

/-- Acceptance by the verifier of `Π_eval^{J,Σ}` implies acceptance of the augmented transcript
by the verifier of `Π_eval^Σ`. -/
theorem cAcceptsSigJ_aug {ℓ : ℕ} (J : Finset ℕ) (hneg : ∀ i < ℓ, (-1 : Fˣ) ∈ lv L i)
    (zp : ℕ → F) (zs : Fin m → F) (v : F) (symOK : Prop) (τ : PTransE F L) (g : Table F m)
    {κ : ℕ} (ξ : Fin κ → L) :
    cAcceptsSigJ ℓ J zp zs v symOK τ g ξ → cAcceptsSig ℓ zp zs v symOK (augE J τ) g ξ := by
  rintro ⟨hsym, hU, hacc⟩
  refine ⟨hsym, ?_, ?_⟩
  · intro t i hi
    rcases i with _ | k
    · exact hU t 0 hi (Or.inl rfl)
    · show augU J τ (k + 1) (ptAt (ξ t) (k + 1 + 1)) ≠ none
      by_cases hk : k + 1 ∈ J
      · simp only [augU, if_pos hk]
        exact hU t (k + 1) hi (Or.inr hk)
      · simp [augU, hk]
  · have h1 := caccepts_aug (cproverOf τ.filled g) ℓ J τ.w0 zp zs v τ.r ξ hacc
    exact accepts_of_W_eq ((cproverOf τ.filled g).aug ℓ J τ.w0) (cproverOf (augE J τ).filled g)
      ℓ τ.w0 zp zs v τ.r ξ rfl rfl (W_aug_eq_augE J hneg τ g) h1

variable {ℓ : ℕ} {zp : ℕ → F} {zs : Fin m → F} {v : F} {δ : ℚ}

/-- **Theorem 6.32(3), rounds `j+1 ∈ [1, ℓ]`.**  The bound of Theorem 6.26 for `Π_eval^{J,Σ}`,
with the knowledge state function of `Π_eval^Σ` applied to the augmented transcript and the
extractor `E` applied to its implicit instance (which the augmentation does not change). -/
theorem crrbr_round_J [Fintype F] [DecidableEq F] {R : ℕ} (J : Finset ℕ)
    (hL : IsSmoothDomain L (m + ℓ + R)) (hδ0 : 0 < δ) (hδ : δ ≤ δstar R) (symOK : Prop) (κ : ℕ)
    (num : Fin (Fintype.card F) ≃ F) {β : ℕ} (int : (Fin β → Bool) ≃ Fin (2 ^ β))
    (τ : PTransE F L) {j : ℕ} (hj : j < ℓ) (hdeg : (τ.s j).natDegree ≤ 1) :
    prob (fun vr : Fin β → Bool => ∃ f : Table F (m + ℓ),
        ¬ cKState (κ := κ) ℓ zp zs v R symOK δ (augE J τ) (cEsig ℓ R (augE J τ))
            (Stage.before j) ∧
        cKState (κ := κ) ℓ zp zs v R symOK δ (augE J (τ.updR j (sampleF num (int vr)))) f
          (.mid (j + 1))) ≤
      ((Nat.card (lv L (j + 1)) : ℚ) + 1) * (1 / Fintype.card F + 1 / 2 ^ β) := by
  have key : ∀ (a : F) (f : Table F (m + ℓ)),
      cKState (κ := κ) ℓ zp zs v R symOK δ (augE J (τ.updR j a)) f (.mid (j + 1)) ↔
        cKState (κ := κ) ℓ zp zs v R symOK δ ((augE J τ).updR j a) f (.mid (j + 1)) :=
    fun a _ => imp_congr_right fun _ => cNotDoomedE_augE_updR J τ j a
  refine le_trans (prob_mono ?_)
    (crrbr_round (zp := zp) (zs := zs) (v := v) hL hδ0 hδ symOK κ num int (augE J τ) hj hdeg)
  rintro vr ⟨f, h1, h2⟩
  exact ⟨f, h1, (key _ f).1 h2⟩

/-- **Theorem 6.32(3), round `ℓ+1`.**  The bound `(1-δ)^κ` of Theorem 6.26 for the verifier of
`Π_eval^{J,Σ}`. -/
theorem crrbr_final_J [Fintype L] {R : ℕ} (J : Finset ℕ) (hL : IsSmoothDomain L (m + ℓ + R))
    (hℓ : 1 ≤ ℓ) (hδ0 : 0 < δ) (hδ : δ ≤ δstar R) (symOK : Prop) {κ : ℕ} {Ω : Type*}
    [Fintype Ω] (pos : Ω ≃ (Fin κ → L)) (τ : PTransE F L) (g : Table F m) :
    prob (fun ω : Ω => ∃ _f : Table F (m + ℓ),
        ¬ cKState (κ := κ) ℓ zp zs v R symOK δ (augE J τ) (cEsig ℓ R (augE J τ)) (.mid ℓ) ∧
        cAcceptsSigJ ℓ J zp zs v symOK τ g (pos ω)) ≤ (1 - δ) ^ κ := by
  have hneg : ∀ i < ℓ, (-1 : Fˣ) ∈ lv L i := fun i hi => lv_neg_one_mem hL (by omega)
  refine le_trans (prob_mono ?_)
    (crrbr_final (zp := zp) (zs := zs) (v := v) hL hℓ hδ0 hδ symOK pos (augE J τ) g)
  rintro ω ⟨f, h1, h2⟩
  exact ⟨f, h1, cAcceptsSigJ_aug J hneg zp zs v symOK τ g (pos ω) h2⟩

end Theorem

end SumFRI
