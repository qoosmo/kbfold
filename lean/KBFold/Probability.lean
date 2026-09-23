/-
KBFold/Probability.lean
Finite uniform probability by counting, and the probabilistic lemmas of §3.1 of
"The Boolean-Kernel Basis": Lemma 3.2 (sequential challenges), Lemma 3.3
(independent queries), Lemma 3.4 (randomised provers).

Modelling conventions.
* No measure theory. For a finite type `Ω`, the uniform probability of an event
  `E : Ω → Prop` is `prob E = #{ω | E ω} / |Ω|`, a rational number (`ℚ`).
  All probabilities and error bounds in the project are rational; this suffices
  for every concrete bound in the paper.
* The expectation of `f : Ω → ℚ` under the uniform distribution is
  `expect f = (∑ ω, f ω) / |Ω|`.
-/
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Finset

namespace KBFold

section Basic

variable {Ω : Type*} [Fintype Ω]

/-- Uniform probability on a finite type, by counting: `Pr[E] = |{ω | E ω}| / |Ω|`
(the probability space of §3.1, and of Lemmas 3.2–3.4). -/
noncomputable def prob (E : Ω → Prop) : ℚ := by
  classical exact ((univ.filter E).card : ℚ) / Fintype.card Ω

/-- Uniform expectation on a finite type: `E[f] = (∑ ω, f ω) / |Ω|`. -/
noncomputable def expect (f : Ω → ℚ) : ℚ := (∑ ω, f ω) / Fintype.card Ω

lemma prob_def (E : Ω → Prop) [DecidablePred E] :
    prob E = ((univ.filter E).card : ℚ) / Fintype.card Ω := by
  unfold prob; congr

lemma prob_nonneg (E : Ω → Prop) : 0 ≤ prob E := by
  classical rw [prob_def]; positivity

lemma prob_le_one (E : Ω → Prop) : prob E ≤ 1 := by
  classical
  rw [prob_def]
  rcases Nat.eq_zero_or_pos (Fintype.card Ω) with h | h
  · simp [h]
  · rw [div_le_one (by exact_mod_cast h)]
    exact_mod_cast card_filter_le _ _

lemma prob_mono {E F : Ω → Prop} (h : ∀ ω, E ω → F ω) : prob E ≤ prob F := by
  classical
  rw [prob_def, prob_def]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast card_le_card (fun ω hω => by simp only [mem_filter] at hω ⊢; exact ⟨hω.1, h ω hω.2⟩)

lemma prob_true [Nonempty Ω] : prob (fun _ : Ω => True) = 1 := by
  classical
  rw [prob_def]; simp

lemma exists_of_prob_pos {E : Ω → Prop} (h : 0 < prob E) : ∃ ω, E ω := by
  classical
  by_contra hne
  push_neg at hne
  rw [prob_def, filter_false_of_mem (fun ω _ => hne ω)] at h
  simp at h

lemma prob_false : prob (fun _ : Ω => False) = 0 := by
  classical rw [prob_def]; simp

/-- Union bound for two events. -/
lemma prob_or_le (E F : Ω → Prop) : prob (fun ω => E ω ∨ F ω) ≤ prob E + prob F := by
  classical
  rw [prob_def, prob_def, prob_def, ← add_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  rw [filter_or]
  exact_mod_cast card_union_le _ _

/-- Union bound over a finite family of events. -/
lemma prob_exists_le {ι : Type*} [Fintype ι] (E : ι → Ω → Prop) :
    prob (fun ω => ∃ i, E i ω) ≤ ∑ i, prob (E i) := by
  classical
  simp_rw [prob_def, ← sum_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have : univ.filter (fun ω => ∃ i, E i ω) = univ.biUnion (fun i => univ.filter (E i)) := by
    ext ω; simp
  rw [this]
  exact_mod_cast card_biUnion_le

/-- Probability of an event of a coordinate-free form: `Pr[E] ≤ k / |Ch i|` as soon as every
fibre along coordinate `i` contains at most `k` points of `E`.  This is the single-round
estimate in the proof of Lemma 3.2. -/
theorem prob_le_of_fibre {ι : Type*} [DecidableEq ι] {Ch : ι → Type*} [∀ i, Fintype (Ch i)]
    [∀ i, Nonempty (Ch i)] [Fintype ι] (i : ι) (E : (∀ j, Ch j) → Prop) [DecidablePred E] (k : ℚ)
    (hk : ∀ ω : ∀ j, Ch j,
      ((univ.filter fun c : Ch i => E (Function.update ω i c)).card : ℚ) ≤ k) :
    prob E ≤ k / Fintype.card (Ch i) := by
  classical
  -- The involution `(ω, c) ↦ (update ω i c, ω i)` of `Ω × Ch i`.
  let Φ : (∀ j, Ch j) × Ch i → (∀ j, Ch j) × Ch i := fun p => (Function.update p.1 i p.2, p.1 i)
  have hΦ : ∀ p, Φ (Φ p) = p := by
    intro p; simp [Φ]
  have h1 : (univ.filter fun p : (∀ j, Ch j) × Ch i => E (Φ p).1).card
      = (univ.filter fun p : (∀ j, Ch j) × Ch i => E p.1).card := by
    apply card_nbij' Φ Φ
    · intro p hp; simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hp ⊢
      exact hp
    · intro p hp; simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hp ⊢
      rw [hΦ]; exact hp
    · intro p _; exact hΦ p
    · intro p _; exact hΦ p
  have h2 : ((univ.filter fun p : (∀ j, Ch j) × Ch i => E p.1).card : ℚ)
      = (univ.filter E).card * Fintype.card (Ch i) := by
    rw [← univ_product_univ, filter_product_left (fun ω => E ω), card_product]; simp
  have h3 : ((univ.filter fun p : (∀ j, Ch j) × Ch i => E (Φ p).1).card : ℚ)
      = ∑ ω : (∀ j, Ch j),
          ((univ.filter fun c : Ch i => E (Function.update ω i c)).card : ℚ) := by
    rw [card_filter, Fintype.sum_prod_type]
    push_cast
    refine sum_congr rfl (fun ω _ => ?_)
    rw [card_filter]; push_cast; rfl
  have hcard : (0 : ℚ) < Fintype.card (Ch i) := by exact_mod_cast Fintype.card_pos
  rw [prob_def, div_le_div_iff₀ (by exact_mod_cast Fintype.card_pos) hcard, ← h2, ← h1, h3]
  calc ∑ ω : (∀ j, Ch j), ((univ.filter fun c : Ch i => E (Function.update ω i c)).card : ℚ)
      ≤ ∑ _ω : (∀ j, Ch j), k := sum_le_sum (fun ω _ => hk ω)
    _ = k * Fintype.card (∀ j, Ch j) := by simp [mul_comm]

/-- **Lemma 3.2 (sequential challenges).**
Rounds are indexed by a finite type `ι` (in the paper `ι = Fin ν`) and `Ω = ∏ᵢ Chᵢ` carries the
uniform distribution.  The event `Eᵢ ⊆ Ch₁ × ⋯ × Chᵢ` of the paper is represented by a predicate
on `Ω`; the paper's hypothesis "for every `(c₁,…,c_{i-1})` at most `kᵢ` values `cᵢ` satisfy
`(c₁,…,cᵢ) ∈ Eᵢ`" then reads: for every `ω`, at most `kᵢ` values `c` satisfy
`Eᵢ (update ω i c)`.  (No hypothesis that `Eᵢ` depends only on the prefix is needed: the
statement holds for arbitrary events, which makes it a generalisation.)  The counts `kᵢ` may be
arbitrary rationals. -/
theorem sequential_challenges {ι : Type*} [Fintype ι] [DecidableEq ι] {Ch : ι → Type*}
    [∀ i, Fintype (Ch i)] [∀ i, Nonempty (Ch i)]
    (E : ι → (∀ j, Ch j) → Prop) [∀ i, DecidablePred (E i)] (k : ι → ℚ)
    (hk : ∀ i (ω : ∀ j, Ch j),
      ((univ.filter fun c : Ch i => E i (Function.update ω i c)).card : ℚ) ≤ k i) :
    prob (fun ω => ∃ i, E i ω) ≤ ∑ i, k i / Fintype.card (Ch i) :=
  (prob_exists_le E).trans (sum_le_sum fun i _ => prob_le_of_fibre i (E i) (k i) (hk i))

end Basic

section Queries

variable {Ω' L : Type*} [Fintype Ω'] [Fintype L] [DecidableEq L]

/-- **Lemma 3.3 (independent queries), identity.**
On `Ω' × L^κ` (with `L^κ = Fin κ → L`) with the uniform distribution,
`Pr[ϖ ∈ A ∧ ξ⁽¹⁾,…,ξ⁽ᵏ⁾ ∈ S(ϖ)] = E_ϖ[1_A(ϖ) · (|S(ϖ)|/|L|)^κ]`.
(`κ ≥ 1` and nonemptiness of `Ω'`, `L` are not needed for the identity.) -/
theorem independent_queries (κ : ℕ) (S : Ω' → Finset L) (A : Ω' → Prop) [DecidablePred A] :
    prob (fun p : Ω' × (Fin κ → L) => A p.1 ∧ ∀ t, p.2 t ∈ S p.1)
      = expect (fun ϖ => if A ϖ then (((S ϖ).card : ℚ) / Fintype.card L) ^ κ else 0) := by
  classical
  rw [prob_def, expect, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
  have hc : ((univ.filter fun p : Ω' × (Fin κ → L) => A p.1 ∧ ∀ t, p.2 t ∈ S p.1).card : ℚ)
      = ∑ ϖ : Ω', if A ϖ then ((S ϖ).card : ℚ) ^ κ else 0 := by
    rw [card_filter, Fintype.sum_prod_type]
    push_cast
    refine sum_congr rfl (fun ϖ _ => ?_)
    by_cases hA : A ϖ
    · simp only [hA, true_and, if_true]
      rw [← natCast_card_filter]
      have : (univ.filter fun ξ : Fin κ → L => ∀ t, ξ t ∈ S ϖ)
          = Fintype.piFinset (fun _ : Fin κ => S ϖ) := by
        ext ξ; simp
      rw [this, Fintype.card_piFinset]; simp
    · simp [hA]
  rw [hc]
  rcases Nat.eq_zero_or_pos (Fintype.card L) with hL | hL
  · rcases Nat.eq_zero_or_pos κ with hκ | hκ
    · subst hκ; simp
    · simp [hL, zero_pow hκ.ne']
  · have hL' : (Fintype.card L : ℚ) ≠ 0 := by exact_mod_cast hL.ne'
    push_cast
    rw [mul_comm, ← div_div, sum_div]
    congr 1
    refine sum_congr rfl (fun ϖ _ => ?_)
    split_ifs <;> simp [div_pow]

/-- **Lemma 3.3 (independent queries), bound.** If `π ≥ 0` and `|S(ϖ)| ≤ π |L|` for every
`ϖ ∈ A`, the probability is at most `Pr[A] π^κ ≤ π^κ`. -/
theorem independent_queries_le [Nonempty L] (κ : ℕ) (S : Ω' → Finset L) (A : Ω' → Prop)
    (π : ℚ) (hπ : 0 ≤ π) (hS : ∀ ϖ, A ϖ → ((S ϖ).card : ℚ) ≤ π * Fintype.card L) :
    prob (fun p : Ω' × (Fin κ → L) => A p.1 ∧ ∀ t, p.2 t ∈ S p.1) ≤ prob A * π ^ κ ∧
      prob A * π ^ κ ≤ π ^ κ := by
  classical
  refine ⟨?_, ?_⟩
  · rw [independent_queries, expect, prob_def, div_mul_eq_mul_div]
    apply div_le_div_of_nonneg_right _ (by positivity)
    rw [card_filter]; push_cast
    rw [sum_mul]
    refine sum_le_sum (fun ϖ _ => ?_)
    have hL : (0 : ℚ) < Fintype.card L := by exact_mod_cast Fintype.card_pos
    split_ifs with hA
    · rw [one_mul]
      apply pow_le_pow_left₀ (by positivity)
      rw [div_le_iff₀ hL]; exact hS ϖ hA
    · simp
  · calc prob A * π ^ κ ≤ 1 * π ^ κ :=
          mul_le_mul_of_nonneg_right (prob_le_one A) (pow_nonneg hπ κ)
      _ = π ^ κ := one_mul _

end Queries

section Randomised

/-- **Lemma 3.4 (randomised provers), averaging form.** A randomised prover is a finitely
supported distribution `w` (on a finite support `s`) over deterministic provers; its success
probability is the `w`-average of the success probabilities `p i` of the deterministic provers
(see `prob_prod_eq_expect` for why, when the prover's coins are uniform and independent of the
challenges). If each `p i ≤ ε`, the average is `≤ ε`. -/
theorem avg_le_of_forall_le {ι : Type*} (s : Finset ι) (w p : ι → ℚ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hsum : ∑ i ∈ s, w i = 1) (ε : ℚ) (hp : ∀ i ∈ s, p i ≤ ε) :
    ∑ i ∈ s, w i * p i ≤ ε := by
  calc ∑ i ∈ s, w i * p i ≤ ∑ i ∈ s, w i * ε :=
        sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hp i hi) (hw i hi)
    _ = ε := by rw [← sum_mul, hsum, one_mul]

/-- **Lemma 3.4 (randomised provers), contrapositive form.** If the average exceeds `ε`, some
deterministic prover in the support (`w i > 0`) exceeds `ε`. -/
theorem exists_of_avg_gt {ι : Type*} (s : Finset ι) (w p : ι → ℚ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hsum : ∑ i ∈ s, w i = 1) (ε : ℚ)
    (h : ε < ∑ i ∈ s, w i * p i) : ∃ i ∈ s, 0 < w i ∧ ε < p i := by
  by_contra hne
  push_neg at hne
  have : ∑ i ∈ s, w i * p i ≤ ∑ i ∈ s, w i * ε := by
    refine sum_le_sum fun i hi => ?_
    rcases (hw i hi).lt_or_eq with hpos | hzero
    · exact mul_le_mul_of_nonneg_left (hne i hi hpos) (hw i hi)
    · simp [← hzero]
  rw [← sum_mul, hsum, one_mul] at this
  exact absurd h (not_lt.mpr this)

/-- Justification of the averaging in Lemma 3.4 for uniform prover coins: on `R × Ω` with the
uniform distribution (coins `R` independent of the challenges `Ω`), the probability of an event
is the average over the coins `ρ` of its probability over `Ω`. -/
theorem prob_prod_eq_expect {R Ω : Type*} [Fintype R] [Fintype Ω] (E : R → Ω → Prop) :
    prob (fun p : R × Ω => E p.1 p.2) = expect (fun ρ => prob (E ρ)) := by
  classical
  rw [prob_def, expect, Fintype.card_prod]
  simp_rw [prob_def]
  rw [← sum_div, div_div, card_filter, Fintype.sum_prod_type]
  push_cast
  rw [mul_comm]
  congr 1
  refine sum_congr rfl (fun ρ _ => ?_)
  rw [card_filter]; push_cast; rfl

end Randomised

end KBFold
