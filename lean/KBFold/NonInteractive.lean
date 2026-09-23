/-
KBFold/NonInteractive.lean
§7.7 of the paper ("The non-interactive scheme", `sec:sound:pq`): the deterministic and
combinatorial content of the passage from Theorem 7.19 (round-by-round knowledge soundness) to
relaxed round-by-round knowledge soundness (Definition `def:rrbr`) of the IOR `Π_eval^Σ`.

* Fibre strings: `fib` (`fib_j`), its inverse `unfib` (`fib_unfib`, `unfib_fib`), equation
  (`eq:fib-hamming`) `relDist_fib`; partial strings over `Σ = F × F` as `ι → Option (F × F)`,
  their distance to full strings `pDist`, the filling `fill` and `relDist_fill_le`.
* The relation `(R_eval)_{≤δ}`: `RelE`, `RelE_full_iff`.
* Lemma `lem:sampling`: `card_sample_preimage_le`, `card_sample_mem_le`, `prob_sample_le`,
  `prob_sample_event_le`, and the uniform query points `prob_equiv_sample`.
* Lemma `lem:cr-unique`, deterministic core: `cr_unique_core`, `cr_unique_eval`.
* Witness sets with erasures `WsetE` (`𝒲^⊥_j`), `densE`, the doomed set `NotDoomedE`/`DoomedE`
  (`𝒟^⊥_δ`), the extractor `Esig` and the knowledge state function `KState` (Definition
  `def:kstate`).
* Lemma `lem:rbr-erasures`: the step `rbr_stepE`, item (1) key deduction `densE_zero_pDist`,
  `Esig_eq_of_densE`; items (1)–(3) `rbr_erasures_one`, `rbr_erasures_round`,
  `rbr_erasures_final`.
* Theorem `thm:rrbr`: `rrbr_round`, `rrbr_final`, `rrbr_trivial`, with the conditions of
  Definition `def:rrbr` on `KState`: `KState_empty`, `KState_full`, `KState_updR`.

Modelling choices.
* `Σ = F × F`; a partial string indexed by `L_{j+1}` is `lv L (j+1) → Option (F × F)` (`none` is
  `⊥`).  The fixed square root `ξ_η` of `η ∈ L_{j+1}` is `sqrtPt η` of `KBFold/Domain.lean`.
* A statement together with a partial transcript of `Π_eval^Σ` is `τ : PTransE F L`: the round
  polynomials `τ.s` (read from the *filled* messages; any filled string of the prescribed length
  encodes a polynomial of degree `≤ 2`, which is a hypothesis where used), the partial strings
  `τ.U 0 = y` (the implicit instance) and `τ.U j` (`1 ≤ j ≤ ℓ-1`, the oracle part of round `j+1`),
  and the challenges `τ.r`.  `τ.filled : PTrans F L` is the transcript of `Π_eval` on the filled
  words `w_j = fib_j^{-1}(ū_j)`, and `τ.w0 = fib_0^{-1}(ȳ)`, to which the development of
  `KBFold/RBR.lean` applies verbatim.
* Erasures in the sumcheck symbols and in the final table only make the verifier reject; the
  verifier of `Π_eval^Σ` (`AcceptsSig`) takes their absence as a proposition `symOK`.
* The challenge `vr_j ∈ {0,1}^β` is `Fin β → Bool`, read as an integer through an arbitrary
  bijection `int : (Fin β → Bool) ≃ Fin (2^β)` (for instance `bitsInt`), and `r_j = φ(vr_j)` with
  `φ(u) = num(u mod |F|)` (`sampleF`).  The query challenge of round `ℓ+1` is modelled by any
  finite type `Ω` with a bijection onto `L^κ` (`prob_equiv_sample`).
* `δ* = (1-ρ)/2 = (1 - 2^{-R})/2` (`δstar R`).
* Transcripts of the IOR are represented by their *stages* (`Stage`): `τ_0 = tr_∅`, `τ_j`
  (`1 ≤ j ≤ ℓ`) and the full transcript.  A transcript ending with a prover message has the stage
  of its prefix, so item 4 of Definition `def:kstate` (and condition 2 of Definition `def:rrbr`)
  holds by construction.
* Outside Lean: the Merkle-collision step of Lemma `lem:cr-unique` and Corollary `cor:pq`
  (the compiler of [CDHZ25]).
-/
import KBFold.RBR

set_option autoImplicit false

open Polynomial Finset

namespace KBFold

variable {F : Type*} [Field F]

/-! ### Fibre strings and partial strings (§7.7, "Fibre strings") -/

section FibreStrings

variable {D : Subgroup Fˣ}

/-- **§7.7, fibre strings:** `fib_j(w) : η ↦ (w(ξ_η), w(-ξ_η))`, with `ξ_η = sqrtPt η` the fixed
square root of `η ∈ D²` (`D = L_j`, `D² = L_{j+1}`). -/
noncomputable def fib (w : D → F) : sqDom D → F × F :=
  fun η => (w (sqrtPt η), w (negPt (sqrtPt η)))

/-- **§7.7, fibre strings:** the inverse `fib_j^{-1}` of `fib_j`: the word taking the first
component of the symbol at `ξ²` on `ξ_{ξ²}`, and the second one on `-ξ_{ξ²}`. -/
noncomputable def unfib (u : sqDom D → F × F) : D → F := by
  classical exact fun ξ => if ξ = sqrtPt (sqPt ξ) then (u (sqPt ξ)).1 else (u (sqPt ξ)).2

/-- **§7.7:** `fib_j ∘ fib_j^{-1} = id` (`fib_j` is onto `Σ^{M_{j+1}}`). -/
theorem fib_unfib (hD : (-1 : Fˣ) ∈ D) (h2 : (2 : F) ≠ 0) (u : sqDom D → F × F) :
    fib (unfib u) = u := by
  classical
  funext η
  have hn : negPt (sqrtPt η) ≠ sqrtPt η := negPt_ne hD h2 _
  simp only [fib, unfib, sqPt_sqrtPt, sqPt_negPt, if_true, hn, if_false]

/-- **§7.7:** `fib_j^{-1} ∘ fib_j = id` (`fib_j` is injective). -/
theorem unfib_fib (hD : (-1 : Fˣ) ∈ D) (w : D → F) : unfib (fib w) = w := by
  classical
  funext ξ
  simp only [unfib, fib]
  split_ifs with h
  · rw [← h]
  · rcases (sqPt_eq_iff hD ξ (sqrtPt (sqPt ξ))).1 (sqPt_sqrtPt _).symm with h' | h'
    · exact absurd h' h
    · rw [← h']

/-- Two words have the same fibre symbol at `η` iff they agree on the fibre over `η`. -/
theorem fib_eq_iff (hD : (-1 : Fˣ) ∈ D) (w c : D → F) (η : sqDom D) :
    fib w η = fib c η ↔ ∀ ξ ∈ fibre η, w ξ = c ξ := by
  constructor
  · intro h ξ hξ
    simp only [fib, Prod.mk.injEq] at h
    have : sqPt ξ = sqPt (sqrtPt η) := by rw [sqPt_sqrtPt]; exact hξ
    rcases (sqPt_eq_iff hD ξ (sqrtPt η)).1 this with rfl | rfl
    · exact h.1
    · exact h.2
  · intro h
    simp only [fib, Prod.mk.injEq]
    exact ⟨h _ (sqrtPt_mem_fibre η), h _ (negPt_mem_fibre (sqrtPt_mem_fibre η))⟩

/-- **Equation (`eq:fib-hamming`):** `Δ(fib_j(w), fib_j(c)) = Δ^fib_j(w, c)`. -/
theorem relDist_fib (hD : (-1 : Fˣ) ∈ D) (w c : D → F) :
    relDist (fib w) (fib c) = fibDist w c := by
  have : disagreeSet (fib w) (fib c) = fibBad w c := by
    ext η
    simp only [disagreeSet, fibBad, Set.mem_setOf_eq, Ne, fib_eq_iff hD, not_forall, exists_prop]
  simp only [relDist, fibDist, hdist, this]

end FibreStrings

section Partial

variable {ι : Type*}

/-- **§7.7:** the filling `ū` of a partial string over `Σ = F × F`: every `⊥` becomes `(0,0)`. -/
def fill (u : ι → Option (F × F)) : ι → F × F := fun η => (u η).getD (0, 0)

/-- The relative Hamming distance `Δ(u, x)` of a partial string `u` to a full string `x`, where
`⊥` entries count as disagreements. -/
noncomputable def pDist {β : Type*} (u : ι → Option β) (x : ι → β) : ℚ :=
  relDist u (fun η => some (x η))

/-- **§7.7:** `Δ(ū, u') ≤ Δ(u, u')` for every full string `u'`. -/
theorem relDist_fill_le [Finite ι] (u : ι → Option (F × F)) (x : ι → F × F) :
    relDist (fill u) x ≤ pDist u x := by
  unfold pDist relDist hdist
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Nat.cast_le.2
  refine Set.ncard_le_ncard (fun η hη => ?_) (Set.toFinite _)
  simp only [disagreeSet, Set.mem_setOf_eq, fill] at hη ⊢
  intro h
  rw [h] at hη
  exact hη rfl

/-- `Δ(u, x) ≤ δ` iff `u` agrees with `x` (in particular is not `⊥`) on at least `(1-δ)|ι|`
positions (the form used in Corollary `cor:pq` and Lemma `lem:cr-unique`). -/
theorem pDist_le_iff {β : Type*} [Finite ι] [Nonempty ι] (u : ι → Option β) (x : ι → β)
    (δ : ℚ) :
    pDist u x ≤ δ ↔ (1 - δ) * Nat.card ι ≤ {η | u η = some (x η)}.ncard := by
  have hpos : (0 : ℚ) < Nat.card ι := by exact_mod_cast Nat.card_pos
  have h := agree_add_hdist u (fun η => some (x η))
  have h' : (({η | u η = some (x η)} : Set ι).ncard : ℚ) + hdist u (fun η => some (x η)) =
      Nat.card ι := by exact_mod_cast h
  unfold pDist relDist
  rw [div_le_iff₀ hpos]
  constructor <;> intro <;> linarith

end Partial

/-! ### Lemma `lem:sampling` -/

section Sampling

variable [Fintype F] [DecidableEq F]

/-- **§7.7, challenges:** the binary reading `int : {0,1}^β → [0, 2^β - 1]` (here the little-endian reading of
`finFunctionFinEquiv`; every statement below holds for an arbitrary bijection). -/
def bitsInt (β : ℕ) : (Fin β → Bool) ≃ Fin (2 ^ β) :=
  (Equiv.arrowCongr (Equiv.refl _) finTwoEquiv.symm).trans finFunctionFinEquiv

/-- **§7.7, challenges:** `φ(u) = num(u mod |F|)` for `u ∈ [0, 2^β - 1]`, with a bijection
`num : [0, |F|-1] → F`. -/
def sampleF (num : Fin (Fintype.card F) ≃ F) {β : ℕ} (u : Fin (2 ^ β)) : F :=
  num ⟨(u : ℕ) % Fintype.card F, Nat.mod_lt _ Fintype.card_pos⟩

/-- **Lemma `lem:sampling`**, preimage count: each `a ∈ F` has at most `2^β/|F| + 1` preimages
under `φ` (the paper: at most `⌈2^β/|F|⌉ < 2^β/|F| + 1`). -/
theorem card_sample_preimage_le (num : Fin (Fintype.card F) ≃ F) (β : ℕ) (a : F) :
    ((univ.filter fun u : Fin (2 ^ β) => sampleF num u = a).card : ℚ) ≤
      (2 ^ β : ℚ) / Fintype.card F + 1 := by
  classical
  have hq : 0 < Fintype.card F := Fintype.card_pos
  have hmaps : ∀ u ∈ univ.filter (fun u : Fin (2 ^ β) => sampleF num u = a),
      (u : ℕ) / Fintype.card F ∈ range (2 ^ β / Fintype.card F + 1) := by
    intro u _
    rw [mem_range, Nat.lt_succ_iff]
    exact Nat.div_le_div_right u.isLt.le
  have hinj : Set.InjOn (fun u : Fin (2 ^ β) => (u : ℕ) / Fintype.card F)
      (univ.filter (fun u : Fin (2 ^ β) => sampleF num u = a) : Set (Fin (2 ^ β))) := by
    intro u hu u' hu' he
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq, sampleF] at hu hu'
    have hm : (u : ℕ) % Fintype.card F = (u' : ℕ) % Fintype.card F := by
      have := hu.trans hu'.symm
      have := num.injective this
      simpa using congrArg Fin.val this
    apply Fin.ext
    rw [← Nat.div_add_mod (u : ℕ) (Fintype.card F), ← Nat.div_add_mod (u' : ℕ) (Fintype.card F), hm]
    simp only at he
    rw [he]
  have hc := card_le_card_of_injOn _ hmaps hinj
  rw [card_range] at hc
  calc ((univ.filter fun u : Fin (2 ^ β) => sampleF num u = a).card : ℚ)
      ≤ ((2 ^ β / Fintype.card F + 1 : ℕ) : ℚ) := by exact_mod_cast hc
    _ ≤ (2 ^ β : ℚ) / Fintype.card F + 1 := by
        have hq' : (0 : ℚ) < Fintype.card F := by exact_mod_cast hq
        have hdm : ((2 ^ β / Fintype.card F : ℕ) : ℚ) * Fintype.card F ≤ 2 ^ β := by
          exact_mod_cast Nat.div_mul_le_self (2 ^ β) (Fintype.card F)
        have : ((2 ^ β / Fintype.card F : ℕ) : ℚ) ≤ (2 ^ β : ℚ) / Fintype.card F := by
          rw [le_div_iff₀ hq']; exact hdm
        push_cast at this ⊢
        linarith

/-- **Lemma `lem:sampling`**, counting form: at most `|S| (2^β/|F| + 1)` values `u` have
`φ(u) ∈ S`. -/
theorem card_sample_mem_le (num : Fin (Fintype.card F) ≃ F) (β : ℕ) (S : Finset F) :
    ((univ.filter fun u : Fin (2 ^ β) => sampleF num u ∈ S).card : ℚ) ≤
      S.card * ((2 ^ β : ℚ) / Fintype.card F + 1) := by
  classical
  have e : (univ.filter fun u : Fin (2 ^ β) => sampleF num u ∈ S) =
      S.biUnion (fun a => univ.filter fun u : Fin (2 ^ β) => sampleF num u = a) := by
    ext u; simp
  rw [e]
  calc ((S.biUnion (fun a => univ.filter fun u : Fin (2 ^ β) => sampleF num u = a)).card : ℚ)
      ≤ ∑ a ∈ S, ((univ.filter fun u : Fin (2 ^ β) => sampleF num u = a).card : ℚ) := by
        exact_mod_cast card_biUnion_le
    _ ≤ ∑ _a ∈ S, ((2 ^ β : ℚ) / Fintype.card F + 1) :=
        sum_le_sum (fun a _ => card_sample_preimage_le num β a)
    _ = S.card * ((2 ^ β : ℚ) / Fintype.card F + 1) := by rw [sum_const, nsmul_eq_mul]

/-- **Lemma `lem:sampling`:** for every `S ⊆ F`,
`Pr_{vr ← {0,1}^β}[φ(int(vr)) ∈ S] ≤ |S| (1/|F| + 2^{-β})`, for any bijection `int`. -/
theorem prob_sample_le (num : Fin (Fintype.card F) ≃ F) {β : ℕ}
    (int : (Fin β → Bool) ≃ Fin (2 ^ β)) (S : Finset F) :
    prob (fun vr : Fin β → Bool => sampleF num (int vr) ∈ S) ≤
      S.card * (1 / Fintype.card F + 1 / 2 ^ β) := by
  classical
  rw [prob_def]
  have hc : (univ.filter fun vr : Fin β → Bool => sampleF num (int vr) ∈ S).card =
      (univ.filter fun u : Fin (2 ^ β) => sampleF num u ∈ S).card :=
    card_equiv int (by simp)
  have hΩ : (Fintype.card (Fin β → Bool) : ℚ) = 2 ^ β := by simp
  rw [hc, hΩ]
  have h2 : (0 : ℚ) < 2 ^ β := by positivity
  rw [div_le_iff₀ h2]
  have := card_sample_mem_le num β S
  have hq : (0 : ℚ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  calc ((univ.filter fun u : Fin (2 ^ β) => sampleF num u ∈ S).card : ℚ)
      ≤ S.card * ((2 ^ β : ℚ) / Fintype.card F + 1) := this
    _ = S.card * (1 / Fintype.card F + 1 / 2 ^ β) * 2 ^ β := by
        field_simp

/-- **Lemma `lem:sampling`**, event form: `Pr_{vr}[P(φ(int(vr)))] ≤ #{a ∈ F : P a} (1/|F| + 2^{-β})`
(the form used in the proof of Theorem `thm:rrbr`). -/
theorem prob_sample_event_le (num : Fin (Fintype.card F) ≃ F) {β : ℕ}
    (int : (Fin β → Bool) ≃ Fin (2 ^ β)) (P : F → Prop) :
    prob (fun vr : Fin β → Bool => P (sampleF num (int vr))) ≤
      ({a : F | P a}.ncard : ℚ) * (1 / Fintype.card F + 1 / 2 ^ β) := by
  classical
  have h := prob_sample_le num int (univ.filter P)
  have e : (fun vr : Fin β → Bool => P (sampleF num (int vr))) =
      (fun vr => sampleF num (int vr) ∈ univ.filter P) := by funext vr; simp
  rw [e]
  refine h.trans (le_of_eq ?_)
  rw [card_filter_eq_ncard]

/-- **Lemma `lem:sampling`**, second sentence: a bijection of finite sample spaces preserves
uniform probabilities; with `pos : {0,1}^{κ(n+R)} ≃ L^κ` the query points are independent and
uniform in `L`. -/
theorem prob_equiv_sample {Ω Ω' : Type*} [Fintype Ω] [Fintype Ω'] (e : Ω ≃ Ω') (E : Ω' → Prop) :
    prob (fun ω => E (e ω)) = prob E := by
  classical
  rw [prob_def, prob_def, Fintype.card_congr e]
  congr 2
  exact_mod_cast card_equiv e (by simp)

end Sampling

/-! ### Lemma `lem:cr-unique` (deterministic core) -/

section CRUnique

variable {L : Subgroup Fˣ}

/-- **Lemma `lem:cr-unique`, deterministic core.**  Let `δ ≤ (1-ρ)/2` with `ρ = 2^n/M` the rate of
`𝒞₀ = RS[L, 2^n]`, and let the partial strings `y, y'` over `Σ = F × F` (indexed by `L₁`) satisfy
`Δ(y, fib₀(Enc f)) ≤ δ` and `Δ(y', fib₀(Enc f')) ≤ δ` (i.e. they agree with these strings on at
least `(1-δ)M/2` fibres, `pDist_le_iff`).  If `f ≠ f'`, then some position `η` is opened in both
(`y η ≠ ⊥ ≠ y' η`) to different values.  The remaining step of the paper — two accepting openings
of one position to different values under one root yield a collision of the random oracle
(salted form of Lemma `lem:merkle`(1)) — concerns the hash function and is not formalised. -/
theorem cr_unique_core [Finite L] (hD : (-1 : Fˣ) ∈ L) (h2 : (2 : F) ≠ 0) {n : ℕ}
    (hn : 2 ^ n ≤ Nat.card L) {δ : ℚ} (hδ : δ ≤ (1 - rate L (2 ^ n)) / 2)
    (y y' : sqDom L → Option (F × F)) (f f' : Table F n)
    (hy : pDist y (fib (Enc L f)) ≤ δ) (hy' : pDist y' (fib (Enc L f')) ≤ δ) (hne : f ≠ f') :
    ∃ η, y η ≠ none ∧ y' η ≠ none ∧ y η ≠ y' η := by
  haveI : Finite (sqDom L) := sqDom_finite
  haveI : Nonempty (sqDom L) := ⟨1⟩
  set K := Nat.card (sqDom L)
  have hM : Nat.card L = 2 * K := card_eq_two_mul_sqDom hD h2
  have hK : (0 : ℚ) < K := by exact_mod_cast Nat.card_pos
  set A := {η | y η = some (fib (Enc L f) η)}
  set A' := {η | y' η = some (fib (Enc L f') η)}
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
  have hsub : sqPt ⁻¹' (A ∩ A') ⊆ agreeSet (Enc L f) (Enc L f') := by
    intro ξ hξ
    obtain ⟨h1, h1'⟩ := hξ
    have hs : y (sqPt ξ) = y' (sqPt ξ) :=
      hcon _ (by rw [h1]; simp) (by rw [h1']; simp)
    have hfe : fib (Enc L f) (sqPt ξ) = fib (Enc L f') (sqPt ξ) := by
      have := h1.symm.trans (hs.trans h1')
      exact Option.some_injective _ this
    exact (fib_eq_iff hD _ _ _).1 hfe ξ rfl
  have hcard : 2 * (A ∩ A').ncard ≤ (agreeSet (Enc L f) (Enc L f')).ncard := by
    rw [← ncard_preimage_sqPt hD h2]
    exact Set.ncard_le_ncard hsub (Set.toFinite _)
  have hEq : Enc L f = Enc L f' := by
    by_contra hE
    have hlt := RS_agree_lt (Enc_mem_RS L f) (Enc_mem_RS L f') hE
    have : (2 ^ n : ℚ) < 2 ^ n := by
      calc (2 ^ n : ℚ) ≤ 2 * (A ∩ A').ncard := hAA
        _ ≤ (agreeSet (Enc L f) (Enc L f')).ncard := by exact_mod_cast hcard
        _ < 2 ^ n := by exact_mod_cast hlt
    exact lt_irrefl _ this
  exact hne (Enc_injective hn hEq)

/-- **Lemma `lem:cr-unique`, last sentence:** if `z = z'` and `v ≠ v'`, then `f ≠ f'`, so
`cr_unique_core` applies. -/
theorem cr_unique_eval {n : ℕ} (f f' : Table F n) (z : Fin n → F) {v v' : F}
    (hv : mle f z = v) (hv' : mle f' z = v') (hne : v ≠ v') : f ≠ f' := by
  rintro rfl; exact hne (hv.symm.trans hv')

end CRUnique

/-! ### The relation `R_eval` and the transcripts of `Π_eval^Σ` -/

/-- **§7.7:** `δ* = (1-ρ)/2` with `ρ = 2^{-R}` the rate of all the codes `𝒞_j`. -/
noncomputable def δstar (R : ℕ) : ℚ := (1 - 1 / 2 ^ R) / 2

section Relation

variable {L : Subgroup Fˣ} {m : ℕ} (ℓ : ℕ) (zp : ℕ → F) (zs : Fin m → F) (v : F) (δ : ℚ)

/-- **§7.7, the relation:** `((z,v), y, f) ∈ (R_eval)_{≤δ}` iff `Δ(y, fib₀(Enc f)) ≤ δ` and
`f~(z) = v`, for a partial string `y` over `Σ` indexed by `L₁` (`⊥` counts as a disagreement). -/
def RelE (y : sqDom L → Option (F × F)) (f : Table F (m + ℓ)) : Prop :=
  pDist y (fib (Enc L f)) ≤ δ ∧ mle f (catPt ℓ zp zs) = v

/-- **§7.7, the relation:** for a full string `y = fib₀(w₀)`, `(R_eval)_{≤δ}` is the relation
`R^δ_eval` of §7.6 (`IsWitness`), by equation (`eq:fib-hamming`). -/
theorem RelE_full_iff (hL : (-1 : Fˣ) ∈ L) (w0 : L → F) (f : Table F (m + ℓ)) :
    RelE ℓ zp zs v δ (fun η => some (fib w0 η)) f ↔ IsWitness ℓ w0 zp zs v δ f := by
  have : pDist (fun η => some (fib w0 η)) (fib (Enc L f)) = relDist (fib w0) (fib (Enc L f)) := by
    unfold pDist relDist hdist disagreeSet
    simp only [Ne, Option.some.injEq]
  rw [RelE, IsWitness, this, relDist_fib hL]

end Relation

/-- **§7.7, the protocol as an IOR:** a statement `y` together with a partial transcript of
`Π_eval^Σ`, given by
* `s i`: the round polynomial `s_{i+1}` read from the filled round-`(i+1)` message;
* `U 0 = y` (the implicit instance, indexed by `L₁`) and, for `1 ≤ j ≤ ℓ-1`, `U j` the oracle
  part of the round-`(j+1)` message (a partial string indexed by `L_{j+1}`);
* `r i`: the challenge `r_{i+1} = φ(vr_{i+1})`. -/
structure PTransE (F : Type*) [Field F] (L : Subgroup Fˣ) where
  /-- filled round polynomials -/
  s : ℕ → F[X]
  /-- partial strings: `U 0 = y`, `U j` = oracle part of round `j+1` -/
  U : (i : ℕ) → lv L (i + 1) → Option (F × F)
  /-- challenges -/
  r : ℕ → F

namespace PTransE

variable {L : Subgroup Fˣ}

/-- The implicit instance `y = U 0`, a partial string indexed by `L₁ = L²`. -/
def y (τ : PTransE F L) : sqDom L → Option (F × F) := τ.U 0

/-- The filled words `w_j = fib_j^{-1}(ū_j)` (`w_0 = fib_0^{-1}(ȳ)`) of §7.7. -/
noncomputable def word (τ : PTransE F L) (j : ℕ) : lv L j → F := unfib (D := lv L j) (fill (τ.U j))

/-- `w_0 = fib_0^{-1}(ȳ)`. -/
noncomputable def w0 (τ : PTransE F L) : L → F := τ.word 0

/-- The transcript of `Π_eval` on the filled words, round polynomials and challenges. -/
noncomputable def filled (τ : PTransE F L) : PTrans F L := ⟨τ.s, τ.word, τ.r⟩

/-- `τ` with the challenge `r_{j+1}` replaced by `a`. -/
def updR (τ : PTransE F L) (j : ℕ) (a : F) : PTransE F L :=
  { τ with r := Function.update τ.r j a }

/-- §7.7: changing `r_{j+1}` commutes with filling. -/
lemma filled_updR (τ : PTransE F L) (j : ℕ) (a : F) :
    (τ.updR j a).filled = τ.filled.updR j a := rfl

/-- §7.7: the words `w_0, w_1, …` of §7.6 computed on the filled transcript are the filled
words `fib_j^{-1}(ū_j)`. -/
lemma Wd_filled (τ : PTransE F L) : Wd τ.w0 τ.filled = τ.word := by
  funext j; cases j <;> rfl

end PTransE

/-! ### Witness sets with erasures and the doomed set `𝒟^⊥_δ` -/

section Erasures

variable {L : Subgroup Fˣ} {m : ℕ} (ℓ : ℕ) (zp : ℕ → F) (zs : Fin m → F) (v : F) (δ : ℚ)

/-- **§7.7, erasures:** `𝒲^⊥_j(c) = {ξ ∈ 𝒲_j(c) : ξ^{2^i} ∉ 𝒰_{i-1} for all i ∈ [1, max(j,1)]}`,
where `𝒰_{i-1}` is the set of erased positions of `U (i-1)` and `𝒲_j` is computed on the filled
words. -/
def WsetE (τ : PTransE F L) (j : ℕ) (c : lv L j → F) : Set L :=
  {ξ | ξ ∈ Wset τ.w0 τ.filled j c ∧ ∀ i < max j 1, τ.U i (ptAt ξ (i + 1)) ≠ none}

/-- `dens^⊥_j(c) = |𝒲^⊥_j(c)| / M`. -/
noncomputable def densE (τ : PTransE F L) (j : ℕ) (c : lv L j → F) : ℚ :=
  ((WsetE τ j c).ncard : ℚ) / Nat.card L

/-- **§7.7, erasures:** `τ_j ∉ 𝒟^⊥_δ` (Definition 7.16 with `dens^⊥_j` in place of `dens_j`). -/
def NotDoomedE (τ : PTransE F L) (j : ℕ) : Prop :=
  SCT v τ.filled j ∧ ∃ c ∈ RS (lv L j) (Nd m ℓ j),
    1 - δ ≤ densE τ j c ∧ vvT v τ.filled j = sigmaJ ℓ zp zs τ.filled j c

/-- **§7.7, erasures:** `τ_j ∈ 𝒟^⊥_δ` (`τ_0` is always doomed). -/
def DoomedE (τ : PTransE F L) (j : ℕ) : Prop := j = 0 ∨ ¬ NotDoomedE ℓ zp zs v δ τ j

variable {ℓ zp zs v δ}

/-- §7.7, erasures: `𝒲^⊥_j(c) ⊆ 𝒲_j(c)`. -/
lemma WsetE_subset (τ : PTransE F L) (j : ℕ) (c : lv L j → F) :
    WsetE τ j c ⊆ Wset τ.w0 τ.filled j c := fun _ h => h.1

/-- §7.7, erasures: `dens^⊥_j(c) ≤ dens_j(c)`. -/
lemma densE_le_dens [Finite L] (τ : PTransE F L) (j : ℕ) (c : lv L j → F) :
    densE τ j c ≤ dens τ.w0 τ.filled j c :=
  div_le_div_of_nonneg_right
    (by exact_mod_cast (Set.ncard_le_ncard (WsetE_subset τ j c) (Set.toFinite _)))
    (Nat.cast_nonneg _)

/-- **§7.7:** without erasures, `𝒲^⊥_j = 𝒲_j` (so `𝒟^⊥_δ` is the doomed set of Definition 7.16). -/
theorem WsetE_eq_of_no_erasure (τ : PTransE F L) (h : ∀ i η, τ.U i η ≠ none) (j : ℕ)
    (c : lv L j → F) : WsetE τ j c = Wset τ.w0 τ.filled j c := by
  ext ξ; exact ⟨fun hξ => hξ.1, fun hξ => ⟨hξ, fun i _ => h i _⟩⟩

/-- **§7.7:** without erasures, `τ_j ∉ 𝒟^⊥_δ` iff `τ_j` is not doomed in the sense of
Definition 7.16 (for the filled transcript). -/
theorem NotDoomedE_iff_of_no_erasure (τ : PTransE F L) (h : ∀ i η, τ.U i η ≠ none) (j : ℕ) :
    NotDoomedE ℓ zp zs v δ τ j ↔ NotDoomed ℓ τ.w0 zp zs v δ τ.filled j := by
  simp only [NotDoomedE, NotDoomed, densE, dens, WsetE_eq_of_no_erasure τ h]

/-- `𝒲^⊥_j(c)` does not depend on the challenge `r_{j+1}`. -/
lemma WsetE_updR (τ : PTransE F L) (j : ℕ) (a : F) (c : lv L j → F) :
    WsetE (τ.updR j a) j c = WsetE τ j c := by
  simp only [WsetE, PTransE.filled_updR]
  rw [show (τ.updR j a).w0 = τ.w0 from rfl, Wset_updR]
  rfl

/-- `τ_j ∉ 𝒟^⊥_δ` does not depend on the challenge `r_{j+1}`. -/
theorem NotDoomedE_updR (τ : PTransE F L) (j : ℕ) (a : F) :
    NotDoomedE ℓ zp zs v δ (τ.updR j a) j ↔ NotDoomedE ℓ zp zs v δ τ j := by
  simp only [NotDoomedE, densE, WsetE_updR, PTransE.filled_updR, sigmaJ_updR,
    vvT_updR τ.filled j a j le_rfl, SCT]
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

/-! ### Lemma `lem:rbr-erasures` -/

section Step

variable {L : Subgroup Fˣ} {m : ℕ} {ℓ : ℕ} {zp : ℕ → F} {zs : Fin m → F} {v : F} {δ : ℚ}

/-- **Lemma `lem:rbr-erasures`, first paragraph of the proof (Lemma 7.17 with `𝒲^⊥`).** Let
`j < ℓ` (the paper's round `j+1`) and `r_{j+1}` good for the filled word `w_j`.  If `c' ∈ 𝒞_{j+1}`
has `dens^⊥_{j+1}(c') ≥ 1-δ`, then `Δ^fib_j(w_j, 𝒞_j) ≤ δ`, `c = dec_j(w_j)` satisfies
`fold_{r_{j+1}}(c) = c'`, and `𝒲^⊥_{j+1}(c') ⊆ 𝒲^⊥_j(c)`. -/
theorem rbr_stepE {R : ℕ} (hL : IsSmoothDomain L (m + ℓ + R)) (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2)
    (τ : PTransE F L) {j : ℕ} (hj : j < ℓ) (hgood : GoodAt ℓ δ m j (τ.word j) (τ.r j))
    (c' : lv L (j + 1) → F) (hc' : c' ∈ RS (lv L (j + 1)) (Nd m ℓ (j + 1)))
    (hdens : 1 - δ ≤ densE τ (j + 1) c') :
    FibDistLE (τ.word j) (RS (lv L j) (2 * Nd m ℓ (j + 1)) : Set _) δ ∧
      wfold (τ.r j) (decAt ℓ δ m j (τ.word j)) = c' ∧
      WsetE τ (j + 1) c' ⊆ WsetE τ j (decAt ℓ δ m j (τ.word j)) := by
  haveI := hL.finite
  have hd : 1 - δ ≤ dens τ.w0 τ.filled (j + 1) c' := hdens.trans (densE_le_dens _ _ _)
  have hgood' : GoodAt ℓ δ m j (Wd τ.w0 τ.filled j) (τ.filled.r j) := by
    rw [PTransE.Wd_filled]; exact hgood
  obtain ⟨hF, hfold, hsub⟩ := rbr_step hL hδ τ.filled hj hgood' c' hc' hd
  rw [PTransE.Wd_filled] at hF hfold hsub
  refine ⟨hF, hfold, fun ξ hξ => ⟨hsub hξ.1, fun i hi => hξ.2 i ?_⟩⟩
  have : max j 1 ≤ max (j + 1) 1 := max_le_max (by omega) le_rfl
  omega

/-- Core of the proof of Lemma `lem:rbr-erasures` (1) and (2): if `r_{j+1} = a` is not bad and
`τ_{j+1} ∉ 𝒟^⊥_δ`, then `c = dec_j(w_j)` exists, the sumcheck checks `1..j` hold,
`dens^⊥_j(c) ≥ 1-δ` and `v_j = σ_j(c)`. -/
theorem rbr_escapeE {R : ℕ} (hL : IsSmoothDomain L (m + ℓ + R)) (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2)
    (τ : PTransE F L) {j : ℕ} (hj : j < ℓ) (a : F)
    (hbad : ¬ BadR ℓ τ.w0 zp zs δ τ.filled j a)
    (hnd : NotDoomedE ℓ zp zs v δ (τ.updR j a) (j + 1)) :
    FibDistLE (τ.word j) (RS (lv L j) (2 * Nd m ℓ (j + 1)) : Set _) δ ∧
      SCT v τ.filled j ∧ 1 - δ ≤ densE τ j (decAt ℓ δ m j (τ.word j)) ∧
      vvT v τ.filled j = sigmaJ ℓ zp zs τ.filled j (decAt ℓ δ m j (τ.word j)) := by
  haveI := hL.finite
  obtain ⟨hSC, c', hc', hdE, hv⟩ := hnd
  have hnd' : NotDoomed ℓ τ.w0 zp zs v δ (τ.filled.updR j a) (j + 1) :=
    ⟨hSC, c', hc', hdE.trans (densE_le_dens _ _ _), hv⟩
  obtain ⟨hF, hSC', -, hv'⟩ := rbr_escape hL hδ τ.filled hj a hbad hnd'
  rw [PTransE.Wd_filled] at hF hv'
  have hgood : GoodAt ℓ δ m j ((τ.updR j a).word j) ((τ.updR j a).r j) := by
    have h := hbad
    simp only [BadR, not_or, not_not] at h
    have e : (τ.updR j a).r j = a := by simp [PTransE.updR]
    rw [e]
    have h1 := h.1
    rw [PTransE.Wd_filled] at h1
    exact h1
  obtain ⟨-, -, hsub⟩ := rbr_stepE hL hδ (τ.updR j a) hj hgood c' hc' hdE
  have hsub' : WsetE (τ.updR j a) (j + 1) c' ⊆ WsetE τ j (decAt ℓ δ m j (τ.word j)) := by
    have := hsub
    rw [WsetE_updR] at this
    exact this
  refine ⟨hF, hSC', hdE.trans ?_, hv'⟩
  exact div_le_div_of_nonneg_right
    (by exact_mod_cast Set.ncard_le_ncard hsub' (Set.toFinite _)) (Nat.cast_nonneg _)

end Step

section ItemOne

variable {L : Subgroup Fˣ} {m : ℕ} {ℓ : ℕ} {δ : ℚ}

/-- **Lemma `lem:rbr-erasures`, proof of (1), key deduction:** `𝒲^⊥_0(c)` consists of points
`ξ` with `ξ² ∉ 𝒰_0` and `w_0 = c` on `{±ξ}`, i.e. lies over the fibres `η` with
`y(η) = fib_0(c)(η)` (in particular `y(η) ≠ ⊥`); so `dens^⊥_0(c) ≥ 1-δ` gives
`Δ(y, fib_0(c)) ≤ δ`.  (Only the inclusion, not the paper's equality "twice the number", is
needed.) -/
theorem densE_zero_pDist (hL0 : (-1 : Fˣ) ∈ L) (h2 : (2 : F) ≠ 0) [Finite L] (τ : PTransE F L)
    (c : L → F) (h : 1 - δ ≤ densE τ 0 c) :
    pDist τ.y (fib c) ≤ δ := by
  haveI : Finite (sqDom L) := sqDom_finite
  haveI : Nonempty (sqDom L) := ⟨1⟩
  haveI : Nonempty L := ⟨1⟩
  set A : Set (sqDom L) := {η | τ.y η = some (fib c η)}
  have hsub : WsetE τ 0 c ⊆ sqPt ⁻¹' A := by
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
  have hcard : (WsetE τ 0 c).ncard ≤ 2 * A.ncard := by
    rw [← ncard_preimage_sqPt hL0 h2]
    exact Set.ncard_le_ncard hsub (Set.toFinite _)
  have hM : Nat.card L = 2 * Nat.card (sqDom L) := card_eq_two_mul_sqDom hL0 h2
  have hpos : (0 : ℚ) < Nat.card L := by exact_mod_cast Nat.card_pos
  rw [pDist_le_iff]
  rw [densE, le_div_iff₀ hpos, hM] at h
  have hc : ((WsetE τ 0 c).ncard : ℚ) ≤ 2 * A.ncard := by exact_mod_cast hcard
  push_cast at h
  linarith

variable (ℓ) in
/-- **Definition `def:kstate` (the algorithm `E`):** read `y`, let `w₀ = fib₀^{-1}(ȳ)`, and output
the decoded table of `w₀` at radius `δ*` if `Δ^fib₀(w₀, 𝒞₀) ≤ δ*`, and the zero table otherwise
(the extractor `Ext` of Definition 7.16 at radius `δ*`).  It depends only on `y = τ.U 0`, not
on `δ`. -/
noncomputable def Esig (R : ℕ) (τ : PTransE F L) : Table F (m + ℓ) := Ext ℓ τ.w0 (δstar R)

/-- **Lemma 6.2 (encoding)**, inverse: a table is the table of kernel coordinates of its
encoding (used for `E(y) = λ[c]` in Lemma `lem:rbr-erasures`(1)). -/
lemma coordsOf_polyOf_Enc [Finite L] {n : ℕ} (hn : 2 ^ n ≤ Nat.card L) (f : Table F n) :
    coordsOf n (polyOf (Enc L f)) = f := by
  rw [Enc, polyOf_ev (degreeLT_mono' hn (ofCoords_mem_degreeLT f)), coordsOf_ofCoords]

/-- **Lemma `lem:rbr-erasures`, proof of (1):** if `c ∈ 𝒞₀` and `dens^⊥_0(c) ≥ 1-δ` with
`δ ≤ δ*`, then `Δ^fib₀(w₀, c) = Δ(ȳ, fib₀(c)) ≤ Δ(y, fib₀(c)) ≤ δ ≤ δ*`, so decoding the filled
word at radius `δ*` gives `c`: `Enc(E(y)) = c`, i.e. `E(y) = λ[c]` (Lemmas 7.3 and 6.2). -/
theorem Esig_eq_of_densE {R : ℕ} (hL : IsSmoothDomain L (m + ℓ + R)) (hℓR : 1 ≤ m + ℓ + R)
    (hδ : δ ≤ δstar R) (τ : PTransE F L) {c : L → F} (hc : c ∈ RS L (2 ^ (m + ℓ)))
    (h : 1 - δ ≤ densE τ 0 c) :
    Enc L (Esig (m := m) ℓ R τ) = c ∧ pDist τ.y (fib c) ≤ δ := by
  classical
  haveI := hL.finite
  have hL0 : (-1 : Fˣ) ∈ L := hL.neg_one_mem hℓR
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_smooth hL hℓR
  have hp := densE_zero_pDist hL0 h2 τ c h
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
  have hE : Esig ℓ R τ = decTable L (m + ℓ) (δstar R) τ.w0 := by simp [Esig, Ext, hF]
  refine ⟨?_, hp⟩
  rw [hE, decTable_spec hn hF]
  exact dec_unique hL0 h2 hδ' hc hfd'

end ItemOne

section Items

variable {L : Subgroup Fˣ} {m : ℕ} {ℓ : ℕ} {zp : ℕ → F} {zs : Fin m → F} {v : F} {δ : ℚ}

/-- **Lemma `lem:rbr-erasures` (1).** Let `0 < δ ≤ δ*` and `ℓ ≥ 1`.  If
`((z,v), y, E(y)) ∉ (R_eval)_{≤δ}`, then, for every round-1 message (`s_1 ∈ F[X]_{<3}`), at most
`M_1 + 2` values of `r_1` make `τ_1 ∉ 𝒟^⊥_δ`. -/
theorem rbr_erasures_one [Fintype F] [DecidableEq F] {R : ℕ} (hL : IsSmoothDomain L (m + ℓ + R))
    (hℓ : 1 ≤ ℓ) (hδ0 : 0 < δ) (hδ : δ ≤ δstar R) (τ : PTransE F L)
    (hnw : ¬ RelE ℓ zp zs v δ τ.y (Esig ℓ R τ))
    (hdeg : (τ.s 0).natDegree ≤ 2) :
    ({a : F | NotDoomedE ℓ zp zs v δ (τ.updR 0 a) 1}.ncard : ℚ) ≤ Nat.card (lv L 1) + 2 := by
  classical
  haveI := hL.finite
  have hsub : {a : F | NotDoomedE ℓ zp zs v δ (τ.updR 0 a) 1} ⊆
      {a : F | BadR ℓ τ.w0 zp zs δ τ.filled 0 a} := by
    intro a hnd
    by_contra hbad
    obtain ⟨hF, -, hdens, hv⟩ := rbr_escapeE hL hδ τ (by omega) a hbad hnd
    set c := decAt ℓ δ m 0 (τ.word 0)
    have e0 : 2 * Nd m ℓ (0 + 1) = 2 ^ (m + ℓ) := by rw [Nd_succ (by omega)]; rfl
    have hc : c ∈ RS L (2 ^ (m + ℓ)) := by
      have h1 : c ∈ RS (lv L 0) (2 * Nd m ℓ (0 + 1)) := (dec_spec hF).1
      have e : RS (lv L 0) (2 * Nd m ℓ (0 + 1)) = RS L (2 ^ (m + ℓ)) := by rw [e0]; rfl
      rw [e] at h1; exact h1
    obtain ⟨hEnc, hp⟩ := Esig_eq_of_densE hL (by omega) hδ τ hc hdens
    apply hnw
    refine ⟨by rw [hEnc]; exact hp, ?_⟩
    have hn : 2 ^ (m + ℓ) ≤ Nat.card L := Nd_le_card (ℓ := ℓ) hL (j := 0) (by omega)
    rw [← coordsOf_polyOf_Enc hn (Esig ℓ R τ), hEnc]
    have hv' : v = sigmaJ ℓ zp zs τ.filled 0 c := hv
    rw [hv', sigmaJ]
    simp only [range_zero, prod_empty, one_mul]
    refine mle_coordsOf_congr _ rfl _ _ (fun i => ?_)
    rw [catPt_eq_zfull]
    simp
  calc ({a : F | NotDoomedE ℓ zp zs v δ (τ.updR 0 a) 1}.ncard : ℚ)
      ≤ {a : F | BadR ℓ τ.w0 zp zs δ τ.filled 0 a}.ncard := by
        exact_mod_cast Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ Nat.card (lv L (0 + 1)) + 2 := card_BadR hL hδ0 hδ τ.filled (by omega) hdeg

/-- **Lemma `lem:rbr-erasures` (2).** Let `0 < δ ≤ δ*` and `1 ≤ j < ℓ` (the paper's round
`j+1 ∈ [2, ℓ]`).  If `τ_j ∈ 𝒟^⊥_δ`, then for every round-`(j+1)` message (partial strings, with
`s_{j+1} ∈ F[X]_{<3}`), at most `M_{j+1} + 2` values of `r_{j+1}` make `τ_{j+1} ∉ 𝒟^⊥_δ`. -/
theorem rbr_erasures_round [Fintype F] [DecidableEq F] {R : ℕ}
    (hL : IsSmoothDomain L (m + ℓ + R)) (hδ0 : 0 < δ) (hδ : δ ≤ δstar R) (τ : PTransE F L)
    {j : ℕ} (hj1 : 1 ≤ j) (hj : j < ℓ) (hdoom : DoomedE ℓ zp zs v δ τ j)
    (hdeg : (τ.s j).natDegree ≤ 2) :
    ({a : F | NotDoomedE ℓ zp zs v δ (τ.updR j a) (j + 1)}.ncard : ℚ) ≤
      Nat.card (lv L (j + 1)) + 2 := by
  classical
  have hnd : ¬ NotDoomedE ℓ zp zs v δ τ j := by
    rcases hdoom with h | h
    · omega
    · exact h
  have hsub : {a : F | NotDoomedE ℓ zp zs v δ (τ.updR j a) (j + 1)} ⊆
      {a : F | BadR ℓ τ.w0 zp zs δ τ.filled j a} := by
    intro a hnd'
    by_contra hbad
    obtain ⟨hF, hSC, hdens, hv⟩ := rbr_escapeE hL hδ τ hj a hbad hnd'
    apply hnd
    have hmem := (dec_spec hF).1
    change decAt ℓ δ m j (τ.word j) ∈ (RS (lv L j) (2 * Nd m ℓ (j + 1)) : Set _) at hmem
    generalize decAt ℓ δ m j (τ.word j) = cs at hmem hdens hv
    rw [Nd_succ (by omega)] at hmem
    exact ⟨hSC, cs, hmem, hdens, hv⟩
  calc ({a : F | NotDoomedE ℓ zp zs v δ (τ.updR j a) (j + 1)}.ncard : ℚ)
      ≤ {a : F | BadR ℓ τ.w0 zp zs δ τ.filled j a}.ncard := by
        exact_mod_cast Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ Nat.card (lv L (j + 1)) + 2 := card_BadR hL hδ0 hδ τ.filled hj hdeg

variable (ℓ zp zs v) in
/-- **§7.7, the verifier of `Π_eval^Σ`:** it rejects if an entry that it reads is `⊥` — the
sumcheck symbols and the final table (whose absence of `⊥` is the proposition `symOK`), and, for
each query point `ξ` and level `i+1 ∈ [1, ℓ]`, the entry at `ξ^{2^{i+1}}` of `U i` — and otherwise
runs the verifier of `Π_eval` on the filled words. -/
def AcceptsSig (symOK : Prop) (τ : PTransE F L) (g : Table F m) {κ : ℕ} (ξ : Fin κ → L) : Prop :=
  symOK ∧ (∀ t, ∀ i < ℓ, τ.U i (ptAt (ξ t) (i + 1)) ≠ none) ∧
    FullAccepts ℓ τ.w0 zp zs v τ.filled g ξ

/-- **Lemma `lem:rbr-erasures` (3).** Let `δ ≤ δ*` and `ℓ ≥ 1`.  If `τ_ℓ ∈ 𝒟^⊥_δ`, then for every
final message `g`, the verifier of `Π_eval^Σ` accepts with probability at most `(1-δ)^κ` over the
query points. -/
theorem rbr_erasures_final [Fintype L] {R : ℕ} (hL : IsSmoothDomain L (m + ℓ + R)) (hℓ : 1 ≤ ℓ)
    (hδ : δ ≤ δstar R) (symOK : Prop) (τ : PTransE F L) (hdoom : DoomedE ℓ zp zs v δ τ ℓ)
    (g : Table F m) (κ : ℕ) :
    prob (fun ξ : Fin κ → L => AcceptsSig ℓ zp zs v symOK τ g ξ) ≤ (1 - δ) ^ κ := by
  classical
  have hR : (0 : ℚ) < 1 / 2 ^ R := by positivity
  have hδ1 : (0 : ℚ) ≤ 1 - δ := by unfold δstar at hδ; linarith
  have hnd : ¬ NotDoomedE ℓ zp zs v δ τ ℓ := by
    rcases hdoom with h | h
    · omega
    · exact h
  haveI := hL.finite
  haveI : Nonempty L := ⟨1⟩
  haveI := lv_finite (L := L) ℓ
  set Pτ := proverOf τ.filled g
  set wl := ev (lv L ℓ) (ofCoords g)
  have hW : ∀ i < ℓ, Pτ.W ℓ τ.w0 τ.filled.r i = Wd τ.w0 τ.filled i := by
    intro i hi
    cases i with
    | zero => rfl
    | succ k => simp only [EvalProver.W, if_neg (show k + 1 ≠ ℓ by omega)]; rfl
  have hWl : Pτ.W ℓ τ.w0 τ.filled.r ℓ = wl := W_last Pτ τ.w0 hℓ τ.filled.r
  have hvv : ∀ i, Pτ.vv v τ.filled.r i = vvT v τ.filled i := by intro i; cases i <;> rfl
  by_cases hSC : SCT v τ.filled ℓ ∧ Pτ.ClosureOK ℓ zp zs v τ.filled.r
  · obtain ⟨hSC, hCl⟩ := hSC
    have hd : 2 ^ m ≤ Nat.card (lv L ℓ) := by
      rw [← Nd_last (ℓ := ℓ)]; exact Nd_le_card hL (by omega)
    have hpoly : polyOf wl = ofCoords g :=
      polyOf_ev (degreeLT_mono' hd (ofCoords_mem_degreeLT g))
    have hσ : vvT v τ.filled ℓ = sigmaJ ℓ zp zs τ.filled ℓ wl := by
      rw [← hvv, hCl, sigmaJ, hpoly]
      congr 1
      · refine prod_congr rfl (fun i hi => ?_)
        rw [zfull_lt zp zs (by simpa using hi)]
      · rw [mle_coordsOf_congr (ofCoords g) (show m + ℓ - ℓ = m by omega)
          (fun i => zfull ℓ zp zs (ℓ + i)) zs (fun i => by rw [← zfull_ge zp zs i]; rfl),
          coordsOf_ofCoords]
        rfl
    have hwl : wl ∈ RS (lv L ℓ) (Nd m ℓ ℓ) := by
      rw [Nd_last]; exact ev_mem_RS (ofCoords_mem_degreeLT g)
    have hdens : densE τ ℓ wl < 1 - δ := by
      by_contra hge
      push_neg at hge
      exact hnd ⟨hSC, wl, hwl, hge, hσ⟩
    -- a query point that passes its checks and reads no `⊥` lies in `𝒲^⊥_ℓ(w_ℓ)`
    have hq : ∀ ξ : L, Pτ.QueryOK ℓ τ.w0 τ.filled.r ξ →
        (∀ i < ℓ, τ.U i (ptAt ξ (i + 1)) ≠ none) → ξ ∈ WsetE τ ℓ wl := by
      intro ξ hξ hU
      refine ⟨?_, fun i hi => hU i (by omega)⟩
      obtain ⟨k, rfl⟩ : ∃ k, ℓ = k + 1 := ⟨ℓ - 1, by omega⟩
      refine ⟨fun i hi => ?_, ?_⟩
      · have := hξ.1 i (by omega)
        simp only [EvalProver.Chk] at this
        rw [hW i (by omega), hW (i + 1) (by omega)] at this
        exact this
      · have := hξ.1 k (by omega)
        simp only [EvalProver.Chk] at this
        rw [hW k (by omega), hWl] at this
        exact this
    calc prob (fun ξ : Fin κ → L => AcceptsSig ℓ zp zs v symOK τ g ξ)
        ≤ prob (fun ξ : Fin κ → L => ∀ t, ξ t ∈ (Set.toFinite (WsetE τ ℓ wl)).toFinset) := by
          apply prob_mono
          intro ξ hacc t
          rw [Set.Finite.mem_toFinset]
          exact hq _ (hacc.2.2.2.2 t) (hacc.2.1 t)
      _ = (((Set.toFinite (WsetE τ ℓ wl)).toFinset.card : ℚ) / Fintype.card L) ^ κ :=
          prob_forall_mem κ _
      _ ≤ (1 - δ) ^ κ := by
          apply pow_le_pow_left₀ (by positivity)
          rw [← Set.ncard_eq_toFinset_card, ← Nat.card_eq_fintype_card]
          exact hdens.le
  · have : ∀ ξ : Fin κ → L, ¬ AcceptsSig ℓ zp zs v symOK τ g ξ := by
      intro ξ hacc
      apply hSC
      refine ⟨fun i hi => ?_, hacc.2.2.2.1⟩
      have := hacc.2.2.1 i hi
      rwa [hvv] at this
    calc prob (fun ξ : Fin κ → L => AcceptsSig ℓ zp zs v symOK τ g ξ)
        = prob (fun _ : Fin κ → L => False) := by
          congr 1; funext ξ; simp only [this ξ]
      _ = 0 := prob_false
      _ ≤ (1 - δ) ^ κ := pow_nonneg hδ1 κ

end Items

/-! ### Definition `def:kstate` and Theorem `thm:rrbr` -/

/-- The stages of a transcript of `Π_eval^Σ`: `tr_∅` (`empty`), the partial transcript `τ_j`
after `j ∈ [1, ℓ]` rounds (`mid j`), and a full transcript with final message `g` and query
points `ξ` (`full g ξ`).  A transcript ending with a prover message has the stage of its prefix
(item 4 of Definition `def:kstate`). -/
inductive Stage (F : Type*) [Field F] (L : Subgroup Fˣ) (m κ : ℕ) : Type _
  /-- `tr_∅` -/
  | empty : Stage F L m κ
  /-- `τ_j`, `1 ≤ j ≤ ℓ` -/
  | mid (j : ℕ) : Stage F L m κ
  /-- the full transcript with final message `g` and query points `ξ` -/
  | full (g : Table F m) (ξ : Fin κ → L) : Stage F L m κ

/-- The stage preceding the challenge of round `j+1`: `tr_∅` for `j = 0`, `τ_j` otherwise. -/
def Stage.before {L : Subgroup Fˣ} {m κ : ℕ} : ℕ → Stage F L m κ
  | 0 => .empty
  | j + 1 => .mid (j + 1)

section KState

variable {L : Subgroup Fˣ} {m κ : ℕ} (ℓ : ℕ) (zp : ℕ → F) (zs : Fin m → F) (v : F) (R : ℕ)
  (symOK : Prop) (δ : ℚ)

/-- **Definition `def:kstate` (knowledge state function of `Π_eval^Σ`)**, for the statement
`((z,v), y)` with `y = τ.U 0`, the transcript data `τ`, and a table `f`:
1. on `tr_∅`: `((z,v), y, f) ∈ (R_eval)_{≤δ}`;
2. on a full transcript: the verifier of `Π_eval^Σ` accepts;
3. on `τ_j`, `j ∈ [1, ℓ]`: `τ_j ∉ 𝒟^⊥_δ` when `δ ∈ (0, δ*]`, and true otherwise;
4. a transcript ending with a prover message: by the stage indexing. -/
def KState (τ : PTransE F L) (f : Table F (m + ℓ)) : Stage F L m κ → Prop
  | .empty => RelE ℓ zp zs v δ τ.y f
  | .mid j => 0 < δ ∧ δ ≤ δstar R → NotDoomedE ℓ zp zs v δ τ j
  | .full g ξ => AcceptsSig ℓ zp zs v symOK τ g ξ

/-- **Definition `def:rrbr`, condition 1 (empty transcript)** for `KState`. -/
theorem KState_empty (τ : PTransE F L) (f : Table F (m + ℓ)) :
    KState (κ := κ) ℓ zp zs v R symOK δ τ f .empty ↔
      RelE ℓ zp zs v δ τ.y f := Iff.rfl

/-- **Definition `def:rrbr`, condition 3 (full transcript)** for `KState`. -/
theorem KState_full (τ : PTransE F L) (f : Table F (m + ℓ)) (g : Table F m) (ξ : Fin κ → L) :
    KState ℓ zp zs v R symOK δ τ f (.full g ξ) ↔ AcceptsSig ℓ zp zs v symOK τ g ξ := Iff.rfl

/-- `KState` on `τ_j` does not depend on the table, nor on the challenge `r_{j+1}` (so it is a
function of the partial transcript `τ_j`). -/
theorem KState_updR (τ : PTransE F L) (f f' : Table F (m + ℓ)) (j : ℕ) (a : F) :
    KState (κ := κ) ℓ zp zs v R symOK δ (τ.updR j a) f (.mid j) ↔
      KState (κ := κ) ℓ zp zs v R symOK δ τ f' (.mid j) := by
  simp only [KState, NotDoomedE_updR]

end KState

section RRBR

variable {L : Subgroup Fˣ} {m : ℕ} {ℓ : ℕ} {zp : ℕ → F} {zs : Fin m → F} {v : F} {δ : ℚ}

/-- **Theorem `thm:rrbr`, rounds `j+1 ∈ [1, ℓ]`.**  Let `δ ∈ (0, δ*]`, `num : [0,|F|-1] ≃ F`, and
`int : {0,1}^β ≃ [0, 2^β-1]`.  For every statement and transcript `tr = τ_j ‖ Π_{j+1}` (the data
`τ`; its challenge `r_{j+1}` is replaced by `φ(vr)`), with `s_{j+1} ∈ F[X]_{<3}`,
`Pr_{vr ← {0,1}^β}[∃ f, KState(tr, E(y)) = 0 ∧ KState(tr ‖ vr, f) = 1]
  ≤ (M_{j+1} + 2)(1/|F| + 2^{-β})`. -/
theorem rrbr_round [Fintype F] [DecidableEq F] {R : ℕ} (hL : IsSmoothDomain L (m + ℓ + R))
    (hδ0 : 0 < δ) (hδ : δ ≤ δstar R) (symOK : Prop) (κ : ℕ)
    (num : Fin (Fintype.card F) ≃ F) {β : ℕ} (int : (Fin β → Bool) ≃ Fin (2 ^ β))
    (τ : PTransE F L) {j : ℕ} (hj : j < ℓ) (hdeg : (τ.s j).natDegree ≤ 2) :
    prob (fun vr : Fin β → Bool => ∃ f : Table F (m + ℓ),
        ¬ KState (κ := κ) ℓ zp zs v R symOK δ τ (Esig ℓ R τ) (Stage.before j) ∧
        KState (κ := κ) ℓ zp zs v R symOK δ (τ.updR j (sampleF num (int vr))) f
          (.mid (j + 1))) ≤
      ((Nat.card (lv L (j + 1)) : ℚ) + 2) * (1 / Fintype.card F + 1 / 2 ^ β) := by
  classical
  have hε : (0 : ℚ) ≤ 1 / Fintype.card F + 1 / 2 ^ β := by positivity
  by_cases h0 : KState (κ := κ) ℓ zp zs v R symOK δ τ (Esig ℓ R τ) (Stage.before j)
  · calc prob (fun vr : Fin β → Bool => ∃ f : Table F (m + ℓ),
            ¬ KState (κ := κ) ℓ zp zs v R symOK δ τ (Esig ℓ R τ) (Stage.before j) ∧
            KState (κ := κ) ℓ zp zs v R symOK δ (τ.updR j (sampleF num (int vr))) f
              (.mid (j + 1)))
          = prob (fun _ : Fin β → Bool => False) := by
            congr 1; funext vr; simp only [h0, not_true_eq_false, false_and, exists_false]
        _ = 0 := prob_false
        _ ≤ _ := by positivity
  · have hcount : ({a : F | NotDoomedE ℓ zp zs v δ (τ.updR j a) (j + 1)}.ncard : ℚ) ≤
        Nat.card (lv L (j + 1)) + 2 := by
      cases j with
      | zero =>
        exact rbr_erasures_one hL (by omega) hδ0 hδ τ h0 hdeg
      | succ k =>
        have hnd : ¬ NotDoomedE ℓ zp zs v δ τ (k + 1) := fun h => h0 (fun _ => h)
        exact rbr_erasures_round hL hδ0 hδ τ (by omega) hj (Or.inr hnd) hdeg
    calc prob (fun vr : Fin β → Bool => ∃ f : Table F (m + ℓ),
            ¬ KState (κ := κ) ℓ zp zs v R symOK δ τ (Esig ℓ R τ) (Stage.before j) ∧
            KState (κ := κ) ℓ zp zs v R symOK δ (τ.updR j (sampleF num (int vr))) f
              (.mid (j + 1)))
          ≤ prob (fun vr : Fin β → Bool =>
              NotDoomedE ℓ zp zs v δ (τ.updR j (sampleF num (int vr))) (j + 1)) := by
            apply prob_mono
            rintro vr ⟨f, -, hK⟩
            exact hK ⟨hδ0, hδ⟩
        _ ≤ ({a : F | NotDoomedE ℓ zp zs v δ (τ.updR j a) (j + 1)}.ncard : ℚ) *
              (1 / Fintype.card F + 1 / 2 ^ β) :=
            prob_sample_event_le num int (fun a => NotDoomedE ℓ zp zs v δ (τ.updR j a) (j + 1))
        _ ≤ _ := mul_le_mul_of_nonneg_right hcount hε

/-- **Theorem `thm:rrbr`, round `ℓ+1`.**  Let `δ ∈ (0, δ*]` and `ℓ ≥ 1`, and let the query
challenge range over a finite type `Ω` with a bijection `pos : Ω ≃ L^κ` (`{0,1}^{κ(n+R)}` in the
paper).  For every statement and transcript `τ_ℓ ‖ g`,
`Pr_{vr ← Ω}[∃ f, KState(τ_ℓ, E(y)) = 0 ∧ KState(τ_ℓ ‖ g ‖ vr, f) = 1] ≤ (1-δ)^κ`. -/
theorem rrbr_final [Fintype L] {R : ℕ} (hL : IsSmoothDomain L (m + ℓ + R)) (hℓ : 1 ≤ ℓ)
    (hδ0 : 0 < δ) (hδ : δ ≤ δstar R) (symOK : Prop) {κ : ℕ} {Ω : Type*} [Fintype Ω]
    (pos : Ω ≃ (Fin κ → L)) (τ : PTransE F L) (g : Table F m) :
    prob (fun ω : Ω => ∃ f : Table F (m + ℓ),
        ¬ KState (κ := κ) ℓ zp zs v R symOK δ τ (Esig ℓ R τ) (.mid ℓ) ∧
        KState ℓ zp zs v R symOK δ τ f (.full g (pos ω))) ≤ (1 - δ) ^ κ := by
  classical
  have hR : (0 : ℚ) < 1 / 2 ^ R := by positivity
  have hδ1 : (0 : ℚ) ≤ 1 - δ := by unfold δstar at hδ; linarith
  by_cases h0 : KState (κ := κ) ℓ zp zs v R symOK δ τ (Esig ℓ R τ) (.mid ℓ)
  · calc prob (fun ω : Ω => ∃ f : Table F (m + ℓ),
            ¬ KState (κ := κ) ℓ zp zs v R symOK δ τ (Esig ℓ R τ) (.mid ℓ) ∧
            KState ℓ zp zs v R symOK δ τ f (.full g (pos ω)))
          = prob (fun _ : Ω => False) := by
            congr 1; funext ω; simp only [h0, not_true_eq_false, false_and, exists_false]
        _ = 0 := prob_false
        _ ≤ _ := pow_nonneg hδ1 κ
  · have hdoom : DoomedE ℓ zp zs v δ τ ℓ := Or.inr (fun h => h0 (fun _ => h))
    calc prob (fun ω : Ω => ∃ f : Table F (m + ℓ),
            ¬ KState (κ := κ) ℓ zp zs v R symOK δ τ (Esig ℓ R τ) (.mid ℓ) ∧
            KState ℓ zp zs v R symOK δ τ f (.full g (pos ω)))
          ≤ prob (fun ω : Ω => AcceptsSig ℓ zp zs v symOK τ g (pos ω)) := by
            apply prob_mono
            rintro ω ⟨f, -, hK⟩
            exact hK
        _ = prob (fun ξ : Fin κ → L => AcceptsSig ℓ zp zs v symOK τ g ξ) :=
            prob_equiv_sample pos (fun ξ => AcceptsSig ℓ zp zs v symOK τ g ξ)
        _ ≤ (1 - δ) ^ κ := rbr_erasures_final hL hℓ hδ symOK τ hdoom g κ

/-- **Theorem `thm:rrbr`, `δ ∉ (0, δ*]`:** the error `ε^rr_j(δ) = 1` bounds every probability. -/
theorem rrbr_trivial {Ω : Type*} [Fintype Ω] (E : Ω → Prop) : prob E ≤ 1 := prob_le_one E

end RRBR

end KBFold
