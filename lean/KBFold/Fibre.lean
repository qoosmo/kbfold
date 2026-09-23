/-
KBFold/Fibre.lean
§7.1–7.3 of the paper, for a single folding step on an arbitrary smooth domain `D`
(the paper's `L_j`, with `L_{j+1} = D²`):
* Definition 7.1 (fibre distance) `fibDist`, `FibDistLE`;
* Lemma 7.2 (fibre distance) `relDist_le_fibDist`, `fibDist_le_iff`;
* Lemma 7.3 (unique fibre decoding) `fib_unique`;
* Definition 7.4 (decoded codeword, decoded table) `dec`, `coordsOf`, `decTable`;
* Lemma 7.6 (folding far words) `far_fold` (from the axiom `bciks_unique` and the line form);
* Lemma 7.7 (fibre errors survive folding) `survive`;
* Definition 7.8 (good challenge) `Good`; Lemma 7.9 (few bad challenges) `ncard_not_good_le`;
* Lemma 7.10 (one folding step) `one_step`.

Conventions.  `D : Subgroup Fˣ` is the domain of the word being folded; the codes are
`RS D (2*d)` (the paper's `𝒞_j`, degree bound `N_j = 2 N_{j+1}`) and `RS (sqDom D) d`
(the paper's `𝒞_{j+1}`).  The hypotheses `-1 ∈ D` and `(2 : F) ≠ 0` (consequences of `D` being a
smooth domain of order `≥ 2`) are explicit where used.  Distances are rational.
-/
import KBFold.WordFold
import KBFold.BCIKS

set_option autoImplicit false

open Polynomial

namespace KBFold

variable {F : Type*} [Field F]

section FibreCount

variable {D : Subgroup Fˣ}

/-- Every set of points of `D²` has a preimage under squaring of exactly twice its size
(each fibre has two points, Definition 2.16). -/
theorem ncard_preimage_sqPt [Finite D] (hD : (-1 : Fˣ) ∈ D) (h2 : (2 : F) ≠ 0)
    (S : Set (sqDom D)) : (sqPt ⁻¹' S).ncard = 2 * S.ncard := by
  refine Set.Finite.induction_on (motive := fun S _ => (sqPt ⁻¹' S).ncard = 2 * S.ncard) S
    (Set.toFinite S) (by simp) ?_
  intro η T hηT hT ih
  have hsplit : (sqPt ⁻¹' (insert η T) : Set D) = fibre η ∪ sqPt ⁻¹' T := by
    ext ξ; simp [fibre]
  have hdisj : Disjoint (fibre η) (sqPt ⁻¹' T : Set D) := by
    rw [Set.disjoint_left]
    intro ξ h1 h2'
    simp only [fibre, Set.mem_setOf_eq, Set.mem_preimage] at h1 h2'
    rw [h1] at h2'; exact hηT h2'
  rw [hsplit, Set.ncard_union_eq hdisj, ncard_fibre hD h2, ih, Set.ncard_insert_of_notMem hηT]
  ring

/-- `|D| = 2 |D²|`. -/
theorem card_eq_two_mul_sqDom [Finite D] (hD : (-1 : Fˣ) ∈ D) (h2 : (2 : F) ≠ 0) :
    Nat.card D = 2 * Nat.card (sqDom D) := by
  have := ncard_preimage_sqPt hD h2 (Set.univ : Set (sqDom D))
  rwa [Set.preimage_univ, Set.ncard_univ, Set.ncard_univ] at this

/-- A set of points of `D` that is a union of fibres (closed under `ξ ↦ -ξ`) has twice as many
points as its image under squaring. -/
theorem ncard_eq_two_mul_image [Finite D] (hD : (-1 : Fˣ) ∈ D) (h2 : (2 : F) ≠ 0)
    (P : Set D) (hP : ∀ ξ ∈ P, negPt ξ ∈ P) : P.ncard = 2 * (sqPt '' P).ncard := by
  have : P = sqPt ⁻¹' (sqPt '' P) := by
    ext ξ
    constructor
    · intro h; exact ⟨ξ, h, rfl⟩
    · rintro ⟨ζ, hζ, he⟩
      rcases (sqPt_eq_iff hD ζ ξ).1 he with rfl | rfl
      · exact hζ
      · have := hP _ hζ; rwa [negPt_negPt hD] at this
  conv_lhs => rw [this]
  exact ncard_preimage_sqPt hD h2 _

end FibreCount

/-! ### Definition 7.1 and Lemma 7.2 (fibre distance) -/

section FibreDistance

variable {D : Subgroup Fˣ}

/-- The set of points `η ∈ D²` over whose fibre `w` and `c` differ somewhere (Definition 7.1). -/
def fibBad (w c : D → F) : Set (sqDom D) := {η | ∃ ξ ∈ fibre η, w ξ ≠ c ξ}

/-- **Definition 7.1 (fibre distance).**
`Δ^fib(w,c) = |{η ∈ D² : w and c differ somewhere on the fibre over η}| / |D²|`. -/
noncomputable def fibDist (w c : D → F) : ℚ := ((fibBad w c).ncard : ℚ) / Nat.card (sqDom D)

/-- **Definition 7.1:** `Δ^fib(w, 𝒞) ≤ δ`, i.e. some element of `𝒞` is within fibre distance `δ`
of `w` (the minimum over the finite nonempty code is attained, so this is the paper's
`min_{c ∈ 𝒞} Δ^fib(w,c) ≤ δ`; its negation is `Δ^fib(w, 𝒞) > δ`). -/
def FibDistLE (w : D → F) (C : Set (D → F)) (δ : ℚ) : Prop := ∃ c ∈ C, fibDist w c ≤ δ

lemma fibDist_nonneg (w c : D → F) : 0 ≤ fibDist w c := by
  unfold fibDist; exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- **Lemma 7.2(1):** `Δ(w,c) ≤ Δ^fib(w,c)`. -/
theorem relDist_le_fibDist [Finite D] (hD : (-1 : Fˣ) ∈ D) (h2 : (2 : F) ≠ 0) (w c : D → F) :
    relDist w c ≤ fibDist w c := by
  have hsub : disagreeSet w c ⊆ sqPt ⁻¹' fibBad w c := by
    intro ξ hξ
    exact ⟨ξ, rfl, hξ⟩
  have h1 : hdist w c ≤ 2 * (fibBad w c).ncard := by
    rw [← ncard_preimage_sqPt hD h2]
    exact Set.ncard_le_ncard hsub (Set.toFinite _)
  have hM := card_eq_two_mul_sqDom hD h2
  have hpos : (0 : ℚ) < Nat.card (sqDom D) := by
    have : Nonempty (sqDom D) := ⟨1⟩
    exact_mod_cast Nat.card_pos
  unfold relDist fibDist
  rw [hM, Nat.cast_mul, Nat.cast_ofNat, div_le_div_iff₀ (by linarith) hpos]
  have : (hdist w c : ℚ) ≤ 2 * (fibBad w c).ncard := by exact_mod_cast h1
  nlinarith

/-- **Lemma 7.2(2):** `Δ^fib(w,c) ≤ δ` iff `w` and `c` agree on every fibre over some set of at
least `(1-δ)|D²|` points of `D²`. -/
theorem fibDist_le_iff [Finite D] (w c : D → F) (δ : ℚ) :
    fibDist w c ≤ δ ↔ ∃ S : Set (sqDom D), (1 - δ) * Nat.card (sqDom D) ≤ S.ncard ∧
      ∀ η ∈ S, ∀ ξ ∈ fibre η, w ξ = c ξ := by
  have hpos : (0 : ℚ) < Nat.card (sqDom D) := by
    have : Nonempty (sqDom D) := ⟨1⟩
    exact_mod_cast Nat.card_pos
  have hcompl := Set.ncard_add_ncard_compl (fibBad w c)
  have hcompl' : ((fibBad w c).ncard : ℚ) + ((fibBad w c)ᶜ).ncard = Nat.card (sqDom D) := by
    exact_mod_cast hcompl
  unfold fibDist
  rw [div_le_iff₀ hpos]
  constructor
  · intro h
    refine ⟨(fibBad w c)ᶜ, by linarith, ?_⟩
    intro η hη ξ hξ
    by_contra hne
    exact hη ⟨ξ, hξ, hne⟩
  · rintro ⟨S, hS, hagree⟩
    have hsub : fibBad w c ⊆ Sᶜ := by
      rintro η ⟨ξ, hξ, hne⟩ hηS
      exact hne (hagree η hηS ξ hξ)
    have h1 : (fibBad w c).ncard ≤ Sᶜ.ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h2 := Set.ncard_add_ncard_compl S
    have h1' : ((fibBad w c).ncard : ℚ) ≤ Sᶜ.ncard := by exact_mod_cast h1
    have h2' : (S.ncard : ℚ) + Sᶜ.ncard = Nat.card (sqDom D) := by exact_mod_cast h2
    linarith

/-- Lemma 7.2(2), complement form: `w = c` on every fibre over a point outside `fibBad`. -/
lemma eq_of_not_fibBad {w c : D → F} {η : sqDom D} (h : η ∉ fibBad w c) :
    ∀ ξ ∈ fibre η, w ξ = c ξ := by
  intro ξ hξ; by_contra hne; exact h ⟨ξ, hξ, hne⟩

/-- **Lemma 7.3 (unique fibre decoding):** if `δ ≤ (1-ρ)/2`, every word is within fibre distance
`δ` of at most one codeword of `RS[D,d]`. -/
theorem fib_unique [Finite D] (hD : (-1 : Fˣ) ∈ D) (h2 : (2 : F) ≠ 0) {d : ℕ} {δ : ℚ}
    (hδ : δ ≤ (1 - rate D d) / 2) (w : D → F) {c c' : D → F} (hc : c ∈ RS D d)
    (hc' : c' ∈ RS D d) (h1 : fibDist w c ≤ δ) (h1' : fibDist w c' ≤ δ) : c = c' :=
  RS_unique_decoding' δ hδ w hc hc' ((relDist_le_fibDist hD h2 w c).trans h1)
    ((relDist_le_fibDist hD h2 w c').trans h1')

end FibreDistance

/-! ### Definition 7.4 (decoded codeword and decoded table) -/

section Decoding

variable {D : Subgroup Fˣ}

/-- **Definition 7.4 (decoded codeword).** `dec(w)` is the codeword of `C` within fibre distance
`δ` of `w` (unique by Lemma 7.3 when `C = RS[D,d]` and `δ ≤ (1-ρ)/2`), and `0` if there is none.
It is defined noncomputably, by choice; see `dec_spec` and `dec_unique`. -/
noncomputable def dec (C : Set (D → F)) (δ : ℚ) (w : D → F) : D → F := by
  classical exact if h : FibDistLE w C δ then h.choose else 0

/-- Definition 7.4: if `Δ^fib(w, C) ≤ δ`, then `dec(w) ∈ C` and `Δ^fib(w, dec(w)) ≤ δ`. -/
theorem dec_spec {C : Set (D → F)} {δ : ℚ} {w : D → F} (h : FibDistLE w C δ) :
    dec C δ w ∈ C ∧ fibDist w (dec C δ w) ≤ δ := by
  classical
  unfold dec; rw [dif_pos h]; exact h.choose_spec

/-- Definition 7.4: `dec(w)` is *the* codeword of `RS[D,d]` within fibre distance `δ`. -/
theorem dec_unique [Finite D] (hD : (-1 : Fˣ) ∈ D) (h2 : (2 : F) ≠ 0) {d : ℕ} {δ : ℚ}
    (hδ : δ ≤ (1 - rate D d) / 2) {w c : D → F} (hc : c ∈ RS D d) (h : fibDist w c ≤ δ) :
    dec (RS D d : Set (D → F)) δ w = c := by
  have hle : FibDistLE w (RS D d : Set (D → F)) δ := ⟨c, hc, h⟩
  obtain ⟨h1, h1'⟩ := dec_spec hle
  exact fib_unique hD h2 hδ w h1 hc h1' h

/-- The table of kernel coordinates of a polynomial `P ∈ F[X]_{<2^n}` (Definition 4.10;
`0` if `P` has no such coordinates). -/
noncomputable def coordsOf (n : ℕ) (P : F[X]) : Table F n := by
  classical exact if h : ∃ lam : Table F n, ofCoords lam = P then h.choose else 0

theorem ofCoords_coordsOf {n : ℕ} {P : F[X]} (hP : P ∈ degreeLT F (2 ^ n)) :
    ofCoords (coordsOf n P) = P := by
  classical
  have h : ∃ lam : Table F n, ofCoords lam = P := (exists_unique_coords P hP).exists
  unfold coordsOf; rw [dif_pos h]; exact h.choose_spec

theorem coordsOf_ofCoords {n : ℕ} (lam : Table F n) : coordsOf n (ofCoords lam) = lam :=
  (exists_unique_coords (ofCoords lam) (ofCoords_mem_degreeLT lam)).unique
    (ofCoords_coordsOf (ofCoords_mem_degreeLT lam)) rfl

/-- **Definition 6.1 (encoding):** `Enc(f) = ev_L(U_f)`, `U_f = ∑_b f(b) K_b`. -/
noncomputable def Enc (L : Subgroup Fˣ) {n : ℕ} (f : Table F n) : L → F := ev L (ofCoords f)

/-- **Lemma 6.2 (encoding)**, linearity: `Enc(a f + g) = a Enc(f) + Enc(g)`. -/
theorem Enc_linear (L : Subgroup Fˣ) {n : ℕ} (a : F) (f g : Table F n) :
    Enc L (fun b => a * f b + g b) = a • Enc L f + Enc L g := by
  have : (fun b => a * f b + g b) = (fun b => a * f b) + g := rfl
  rw [Enc, this, ofCoords_add, ofCoords_smul, ev_add, ev_C_mul]
  rfl

/-- **Lemma 6.2 (encoding)**, injectivity: if `2^n ≤ |L|` then `Enc` is injective. -/
theorem Enc_injective {L : Subgroup Fˣ} [Finite L] {n : ℕ} (hn : 2 ^ n ≤ Nat.card L) :
    Function.Injective (Enc L (n := n) (F := F)) := by
  intro f f' h
  have := ev_injOn hn (ofCoords_mem_degreeLT f) (ofCoords_mem_degreeLT f') h
  rw [← coordsOf_ofCoords f, this, coordsOf_ofCoords]

/-- **Lemma 6.2 (encoding)**, image: `Enc(f) ∈ 𝒞₀ = RS[L, 2^n]`. -/
theorem Enc_mem_RS (L : Subgroup Fˣ) {n : ℕ} (f : Table F n) : Enc L f ∈ RS L (2 ^ n) :=
  ev_mem_RS (ofCoords_mem_degreeLT f)

/-- **Lemma 6.2 (encoding)**, surjectivity and inverse: for `c ∈ RS[L, 2^n]` (with `2^n ≤ |L|`)
the table of kernel coordinates of `P_c` encodes to `c`. -/
theorem Enc_coordsOf {L : Subgroup Fˣ} [Finite L] {n : ℕ} (hn : 2 ^ n ≤ Nat.card L)
    {c : L → F} (hc : c ∈ RS L (2 ^ n)) : Enc L (coordsOf n (polyOf c)) = c := by
  obtain ⟨hP, hPc⟩ := polyOf_spec hn hc
  rw [Enc, ofCoords_coordsOf hP, hPc]

/-- **Definition 7.4 (decoded table):** the table `f*` of kernel coordinates of `P_{dec₀(w)}`,
i.e. the unique table with `Enc(f*) = dec₀(w)` (`decTable_spec`). -/
noncomputable def decTable (L : Subgroup Fˣ) (n : ℕ) (δ : ℚ) (w : L → F) : Table F n :=
  coordsOf n (polyOf (dec (RS L (2 ^ n) : Set (L → F)) δ w))

/-- Definition 7.4: if `Δ^fib₀(w, 𝒞₀) ≤ δ`, then `Enc(f*) = dec₀(w)`. -/
theorem decTable_spec {L : Subgroup Fˣ} [Finite L] {n : ℕ} (hn : 2 ^ n ≤ Nat.card L) {δ : ℚ}
    {w : L → F} (h : FibDistLE w (RS L (2 ^ n) : Set (L → F)) δ) :
    Enc L (decTable L n δ w) = dec (RS L (2 ^ n) : Set (L → F)) δ w :=
  Enc_coordsOf hn (dec_spec h).1

end Decoding

/-! ### Lemmas 7.6 and 7.7 (two folding lemmas) -/

section Folding

variable {D : Subgroup Fˣ}

/-- If the even and odd parts of `T` lie in `F[X]_{<d}`, then `T ∈ F[X]_{<2d}`. -/
lemma mem_degreeLT_of_parts {d : ℕ} {T : F[X]} (hE : evenPart T ∈ degreeLT F d)
    (hO : oddPart T ∈ degreeLT F d) : T ∈ degreeLT F (2 * d) := by
  rw [mem_degreeLT, degree_lt_iff_coeff_zero] at *
  intro m hm
  rcases Nat.even_or_odd' m with ⟨i, rfl | rfl⟩
  · rw [← coeff_evenPart]; exact hE i (by omega)
  · rw [← coeff_oddPart]; exact hO i (by omega)

/-- **Lemma 7.6 (folding far words).** Let `D` be a smooth domain of order `2^μ` with `μ ≥ 1`,
`1 ≤ d` with `2d ≤ |D|` (so that `𝒞 = RS[D,2d]` and `𝒞' = RS[D²,d]` have the same rate `ρ`),
and `0 < δ ≤ (1-ρ)/2`.  If `Δ^fib(w, 𝒞) > δ`, then at most `|D²|` values `r ∈ F` satisfy
`Δ(fold_r(w), 𝒞') ≤ δ`.  (Proof: the axiom `bciks_unique` applied to the line form
`fold_r(w) = u⁰ + r u¹` of Lemma 5.7.) -/
theorem far_fold [Fintype F] {μ : ℕ} (hD : IsSmoothDomain D μ) (hμ : 1 ≤ μ) {d : ℕ}
    (hd : 1 ≤ d) (hdD : 2 * d ≤ Nat.card D) {δ : ℚ} (hδ0 : 0 < δ)
    (hδ : δ ≤ (1 - rate (sqDom D) d) / 2) (w : D → F)
    (hfar : ¬ FibDistLE w (RS D (2 * d) : Set (D → F)) δ) :
    {r : F | DistLE (wfold r w) (RS (sqDom D) d : Set (sqDom D → F)) δ}.ncard
      ≤ Nat.card (sqDom D) := by
  haveI := hD.finite
  have hneg : (-1 : Fˣ) ∈ D := hD.neg_one_mem hμ
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_smooth hD hμ
  have hM := card_eq_two_mul_sqDom hneg h2
  by_contra hlt
  push_neg at hlt
  have hS : Nat.card (sqDom D) <
      {r : F | DistLE (lineU0 w + r • lineU1 w) (RS (sqDom D) d : Set (sqDom D → F)) δ}.ncard := by
    simpa only [← wfold_line] using hlt
  obtain ⟨L', hL', c0, hc0, c1, hc1, hagree⟩ :=
    bciks_unique (sqDom D) (μ - 1) (hD.sqDom_smooth hμ) d hd (by omega) δ hδ0 hδ _ _ hS
  have hdD' : d ≤ Nat.card (sqDom D) := by omega
  obtain ⟨hP0, hP0c⟩ := polyOf_spec hdD' hc0
  obtain ⟨hP1, hP1c⟩ := polyOf_spec hdD' hc1
  set Te : F[X] := polyOf c0 + polyOf c1
  set To : F[X] := C 2 * polyOf c0 + polyOf c1
  set T : F[X] := expand F 2 Te + X * expand F 2 To
  have hTe : Te ∈ degreeLT F d := Submodule.add_mem _ hP0 hP1
  have hTo : To ∈ degreeLT F d := by
    refine Submodule.add_mem _ ?_ hP1
    rw [← smul_eq_C_mul]; exact Submodule.smul_mem _ _ hP0
  have hE : evenPart T = Te := (even_odd_unique Te To).1
  have hO : oddPart T = To := (even_odd_unique Te To).2
  have hT : T ∈ degreeLT F (2 * d) := mem_degreeLT_of_parts (by rw [hE]; exact hTe)
    (by rw [hO]; exact hTo)
  apply hfar
  refine ⟨ev D T, ev_mem_RS hT, (fibDist_le_iff _ _ δ).2 ⟨L', hL', ?_⟩⟩
  intro η hη ξ hξ
  rw [mem_fibre] at hξ
  obtain ⟨h0, h1⟩ := hagree η hη
  have he : evenW w η = Te.eval ((η : Fˣ) : F) := by
    rw [evenW_line, Pi.add_apply, h0, h1]
    simp only [Te, eval_add]
    rw [← congrFun hP0c η, ← congrFun hP1c η]; rfl
  have ho : oddW w η = To.eval ((η : Fˣ) : F) := by
    rw [oddW_line, Pi.add_apply, Pi.smul_apply, h0, h1]
    simp only [To, eval_add, eval_mul, eval_C]
    rw [← congrFun hP0c η, ← congrFun hP1c η]; simp [ev, two_smul, two_mul]
  rw [eval_pos_split hneg h2 w ξ, hξ, he, ho]
  simp only [ev]
  rw [eval_even_odd T, hE, hO, ← hξ, val_sqPt]

/-- **Lemma 7.7 (fibre errors survive folding)**, core form: if `w` and `c` differ somewhere on
the fibre over `η ∈ D²`, two challenges `r, r'` with `fold_r(w)(η) = fold_r(c)(η)` are equal. -/
theorem survive_eq (hD : (-1 : Fˣ) ∈ D) (h2 : (2 : F) ≠ 0) {w c : D → F} {η : sqDom D}
    (hη : ∃ ξ ∈ fibre η, w ξ ≠ c ξ) {r r' : F} (hr : wfold r w η = wfold r c η)
    (hr' : wfold r' w η = wfold r' c η) : r = r' := by
  have hlin : ∀ r, wfold r w η - wfold r c η = lineU0 (w - c) η + r * lineU1 (w - c) η := by
    intro r
    rw [← Pi.sub_apply, ← wfold_sub, wfold_line]; simp
  have e1 : lineU0 (w - c) η + r * lineU1 (w - c) η = 0 := by rw [← hlin, hr, sub_self]
  have e2 : lineU0 (w - c) η + r' * lineU1 (w - c) η = 0 := by rw [← hlin, hr', sub_self]
  by_contra hne
  have hu1 : lineU1 (w - c) η = 0 := by
    have : (r - r') * lineU1 (w - c) η = 0 := by linear_combination e1 - e2
    rcases mul_eq_zero.1 this with h | h
    · exact absurd (sub_eq_zero.1 h) hne
    · exact h
  have hu0 : lineU0 (w - c) η = 0 := by rw [hu1, mul_zero, add_zero] at e1; exact e1
  have hev : evenW (w - c) η = 0 := by rw [evenW_line]; simp [hu0, hu1]
  have hod : oddW (w - c) η = 0 := by rw [oddW_line]; simp [hu0, hu1]
  obtain ⟨ξ, hξ, hne'⟩ := hη
  have := (vanish_fibre_iff hD h2 (w - c) η).2 ⟨hev, hod⟩ ξ hξ
  exact hne' (sub_eq_zero.1 this)

/-- **Lemma 7.7 (fibre errors survive folding).** If `w` and `c` differ somewhere on the fibre
over `η ∈ D²`, there is at most one `r ∈ F` with `fold_r(w)(η) = fold_r(c)(η)`. -/
theorem survive (hD : (-1 : Fˣ) ∈ D) (h2 : (2 : F) ≠ 0) {w c : D → F} {η : sqDom D}
    (hη : ∃ ξ ∈ fibre η, w ξ ≠ c ξ) :
    {r : F | wfold r w η = wfold r c η}.ncard ≤ 1 := by
  by_cases hfin : {r : F | wfold r w η = wfold r c η}.Finite
  · exact (Set.ncard_le_one hfin).2 (fun r hr r' hr' => survive_eq hD h2 hη hr hr')
  · rw [Set.Infinite.ncard hfin]; exact zero_le_one

end Folding

/-! ### Definition 7.8, Lemmas 7.9 and 7.10 (good challenges, one folding step) -/

section Good

variable {D : Subgroup Fˣ}

/-- **Definition 7.8 (good challenge).**  For a word `w` on `D` (the paper's `L_{j-1}`), codes
`𝒞 = RS[D,2d]` and `𝒞' = RS[D²,d]`: `r` is good for `w` if
1. when `Δ^fib(w, 𝒞) > δ`: `Δ(fold_r(w), 𝒞') > δ`;
2. when `Δ^fib(w, 𝒞) ≤ δ`, with `c = dec(w)`: for every `η ∈ D²` over whose fibre `w` and `c`
   differ somewhere, `fold_r(w)(η) ≠ fold_r(c)(η)`. -/
def Good (δ : ℚ) (d : ℕ) (w : D → F) (r : F) : Prop :=
  (¬ FibDistLE w (RS D (2 * d) : Set (D → F)) δ →
      ¬ DistLE (wfold r w) (RS (sqDom D) d : Set (sqDom D → F)) δ) ∧
  (FibDistLE w (RS D (2 * d) : Set (D → F)) δ →
      ∀ η : sqDom D, (∃ ξ ∈ fibre η, w ξ ≠ dec (RS D (2 * d) : Set (D → F)) δ w ξ) →
        wfold r w η ≠ wfold r (dec (RS D (2 * d) : Set (D → F)) δ w) η)

/-- **Lemma 7.9 (few bad challenges).** At most `|D²|` (the paper's `M_j`) values `r ∈ F` are
not good for `w`. -/
theorem ncard_not_good_le [Fintype F] {μ : ℕ} (hD : IsSmoothDomain D μ) (hμ : 1 ≤ μ) {d : ℕ}
    (hd : 1 ≤ d) (hdD : 2 * d ≤ Nat.card D) {δ : ℚ} (hδ0 : 0 < δ)
    (hδ : δ ≤ (1 - rate (sqDom D) d) / 2) (w : D → F) :
    {r : F | ¬ Good δ d w r}.ncard ≤ Nat.card (sqDom D) := by
  classical
  haveI := hD.finite
  have hneg : (-1 : Fˣ) ∈ D := hD.neg_one_mem hμ
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_smooth hD hμ
  by_cases hfar : FibDistLE w (RS D (2 * d) : Set (D → F)) δ
  · -- case 2: each bad `r` has a witness point `η` over which it is bad, and a point `η`
    -- witnesses at most one `r` (Lemma 7.7)
    set c := dec (RS D (2 * d) : Set (D → F)) δ w
    have hbad : ∀ r ∈ {r : F | ¬ Good δ d w r},
        ∃ η, η ∈ fibBad w c ∧ wfold r w η = wfold r c η := by
      intro r hr
      simp only [Set.mem_setOf_eq, Good, not_and_or] at hr
      rcases hr with h | h
      · exact absurd (fun hf => (hf hfar).elim) h
      · by_contra hne
        push_neg at hne
        exact h (fun _ η hη => hne η hη)
    choose! f hf using hbad
    calc {r : F | ¬ Good δ d w r}.ncard ≤ (fibBad w c).ncard :=
          Set.ncard_le_ncard_of_injOn f (fun r hr => (hf r hr).1)
            (fun r hr r' hr' he => survive_eq hneg h2 (hf r hr).1 (hf r hr).2
              (by rw [he]; exact (hf r' hr').2))
      _ ≤ Nat.card (sqDom D) := by
          rw [← Set.ncard_univ]; exact Set.ncard_le_ncard (Set.subset_univ _)
  · -- case 1: Lemma 7.6
    have hsub : {r : F | ¬ Good δ d w r} ⊆
        {r : F | DistLE (wfold r w) (RS (sqDom D) d : Set (sqDom D → F)) δ} := by
      intro r hr
      simp only [Set.mem_setOf_eq, Good, not_and_or] at hr
      rcases hr with h | h
      · by_contra hne; exact h (fun _ => hne)
      · exact absurd (fun hf => absurd hf hfar) h
    exact (Set.ncard_le_ncard hsub (Set.toFinite _)).trans
      (far_fold hD hμ hd hdD hδ0 hδ w hfar)

/-- **Lemma 7.10 (one folding step).** Let `r` be good for `w`, `c' ∈ RS[D²,d]` and
`Y = {η ∈ D² : fold_r(w)(η) = c'(η)}` with `|Y| ≥ (1-δ)|D²|`.  Then `Δ^fib(w, 𝒞) ≤ δ`, the
codeword `c = dec(w)` satisfies `fold_r(c) = c'`, and `w = c` on the fibre over every `η ∈ Y`. -/
theorem one_step {μ : ℕ} (hD : IsSmoothDomain D μ) (hμ : 1 ≤ μ) {d : ℕ} {δ : ℚ} (hδ : δ ≤ (1 - rate (sqDom D) d) / 2) (w : D → F)
    (r : F) (hgood : Good δ d w r) (c' : sqDom D → F) (hc' : c' ∈ RS (sqDom D) d)
    (hY : (1 - δ) * Nat.card (sqDom D) ≤ (agreeSet (wfold r w) c').ncard) :
    FibDistLE w (RS D (2 * d) : Set (D → F)) δ ∧
    wfold r (dec (RS D (2 * d) : Set (D → F)) δ w) = c' ∧
    ∀ η ∈ agreeSet (wfold r w) c', ∀ ξ ∈ fibre η,
      w ξ = dec (RS D (2 * d) : Set (D → F)) δ w ξ := by
  haveI := hD.finite
  have hneg : (-1 : Fˣ) ∈ D := hD.neg_one_mem hμ
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_smooth hD hμ
  have hM := card_eq_two_mul_sqDom hneg h2
  have hpos : (0 : ℚ) < Nat.card (sqDom D) := by
    have : Nonempty (sqDom D) := ⟨1⟩
    exact_mod_cast Nat.card_pos
  -- `Δ(fold_r(w), c') ≤ δ`
  have hdist : relDist (wfold r w) c' ≤ δ := by
    have h := agree_add_hdist (wfold r w) c'
    have h' : ((agreeSet (wfold r w) c').ncard : ℚ) + hdist (wfold r w) c'
        = Nat.card (sqDom D) := by exact_mod_cast h
    unfold relDist
    rw [div_le_iff₀ hpos]
    linarith
  have hclose : FibDistLE w (RS D (2 * d) : Set (D → F)) δ := by
    by_contra hfar
    exact hgood.1 hfar ⟨c', hc', hdist⟩
  set c := dec (RS D (2 * d) : Set (D → F)) δ w
  obtain ⟨hcC, hcw⟩ := dec_spec hclose
  have hfc : wfold r c ∈ RS (sqDom D) d := wfold_mem_RS hneg h2 r hcC
  -- `fold_r(c)` agrees with `fold_r(w)` on at least `(1-δ)|D²|` points
  obtain ⟨S, hS, hSagree⟩ := (fibDist_le_iff w c δ).1 hcw
  have hagr1 : (1 - δ) * Nat.card (sqDom D) ≤ (agreeSet (wfold r c) (wfold r w)).ncard := by
    refine hS.trans ?_
    have : S ⊆ agreeSet (wfold r c) (wfold r w) := by
      intro η hη
      exact (wfold_congr r (hSagree η hη)).symm
    exact_mod_cast Set.ncard_le_ncard this (Set.toFinite _)
  have hagr := agree_trans_frac (wfold r c) (wfold r w) c' _ _ hagr1 hY
  have hrate : rate (sqDom D) d * Nat.card (sqDom D) = d := by
    rw [rate, div_mul_cancel₀ _ hpos.ne']
  have heq : wfold r c = c' := by
    by_contra hne
    have hlt := RS_agree_lt hfc hc' hne
    have hlt' : ((agreeSet (wfold r c) c').ncard : ℚ) < d := by exact_mod_cast hlt
    have : (d : ℚ) ≤ (1 - δ + (1 - δ) - 1) * Nat.card (sqDom D) := by
      rw [← hrate]
      have : rate (sqDom D) d ≤ 1 - δ + (1 - δ) - 1 := by linarith
      exact mul_le_mul_of_nonneg_right this hpos.le
    linarith
  refine ⟨hclose, heq, ?_⟩
  intro η hη ξ hξ
  by_contra hne
  apply hgood.2 hclose η ⟨ξ, hξ, hne⟩
  rw [show wfold r w η = c' η from hη, ← heq]

end Good

end KBFold
