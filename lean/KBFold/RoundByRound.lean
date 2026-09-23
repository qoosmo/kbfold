/-
KBFold/RoundByRound.lean
Interactive oracle proofs, (round-by-round) soundness and knowledge soundness, the sumcheck
protocol, and evaluation binding: §3.1–3.4 of "The Boolean-Kernel Basis"
(Definitions 3.5–3.7, Lemmas 3.8, 3.9, 3.12; the IOP form of Lemma 3.4).

Modelling of an IOP (Definition 3.1) and its restrictions.
* `ν` rounds; challenge sets `Ch : Fin ν → Type` (finite, nonempty). Round `i : Fin ν` is the
  paper's round `i+1` (0-based indexing throughout).
* One message type `M` for all rounds (any family of message sets embeds into one type, e.g.
  a sigma type; quantifications "for every message `mᵢ`" then range over all of `M`).
* A transcript entry is a pair `(m, ⟨i, c⟩)` of a message and a challenge tagged with its round;
  a partial transcript is a list of entries, and `IsPartial τ i` says that `τ` is a well-formed
  partial transcript of `i` rounds (its entries carry the round tags `0, …, i-1`).  The instance
  `x` is kept as a separate argument (the paper's `τ = (x, m₁, c₁, …)`).
* Oracles are not modelled separately: the verifier is an arbitrary predicate
  `V : X → Transcript → Prop` on (instance, full transcript), which covers any deterministic
  decision procedure that queries the oracle parts of the instance and of the messages.
* A deterministic prover is a function `X → Transcript → M` (partial transcript ↦ next message).
* The running time of the extractor (Definition 3.7) is not modelled: the extractor is an
  arbitrary function.  As the paper remarks, Lemmas 3.8 and 3.12 do not use it.
* Probabilities are rational and computed by counting (`KBFold.prob`), over `Ω = ∏ᵢ Chᵢ`.
-/
import KBFold.Probability
import KBFold.Multilinear
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Tactic.Linarith

open Finset

namespace KBFold

section IOP

variable {ν : ℕ} {Ch : Fin ν → Type*} {X W M : Type*}

/-- A transcript entry: the prover's message of a round and the verifier's challenge of that
round, tagged with the round index (Definition 3.1). -/
abbrev Entry (Ch : Fin ν → Type*) (M : Type*) := M × (Σ i : Fin ν, Ch i)

/-- Partial transcripts (without the instance), as lists of entries (§3.1). -/
abbrev Transcript (Ch : Fin ν → Type*) (M : Type*) := List (Entry Ch M)

/-- `τ` is a partial transcript of `i` rounds: its entries are tagged `0, 1, …, i-1`. -/
def IsPartial (τ : Transcript Ch M) (i : ℕ) : Prop :=
  τ.map (fun e => (e.2.1 : ℕ)) = List.range i

/-- A deterministic prover (§3.1): maps an instance and a partial transcript of `i` rounds to
the next message `m_{i+1}`. -/
abbrev Prover (Ch : Fin ν → Type*) (X M : Type*) := X → Transcript Ch M → M

/-- The partial transcript `τᵢ` after `i` rounds of the interaction of `P` on `x`, for the
challenge vector `ω = (c₁,…,c_ν)`. -/
def trace (P : Prover Ch X M) (x : X) (ω : ∀ i, Ch i) : ℕ → Transcript Ch M
  | 0 => []
  | i + 1 =>
    if h : i < ν then trace P x ω i ++ [(P x (trace P x ω i), ⟨⟨i, h⟩, ω ⟨i, h⟩⟩)]
    else trace P x ω i

/-- The message of round `i` (the paper's `m_{i+1}`), a function of the earlier challenges. -/
def msg (P : Prover Ch X M) (x : X) (ω : ∀ i, Ch i) (i : Fin ν) : M := P x (trace P x ω i)

variable (P : Prover Ch X M) (x : X)

lemma trace_succ (ω : ∀ i, Ch i) (i : Fin ν) :
    trace P x ω (i + 1) = trace P x ω i ++ [(msg P x ω i, ⟨i, ω i⟩)] := by
  simp [trace, msg, i.isLt]

lemma isPartial_trace (ω : ∀ i, Ch i) : ∀ i ≤ ν, IsPartial (trace P x ω i) i
  | 0, _ => rfl
  | i + 1, hi => by
    have h := trace_succ P x ω ⟨i, hi⟩
    simp only at h
    rw [h, IsPartial, List.map_append, isPartial_trace ω i (by omega), List.range_succ]
    rfl

/-- `τᵢ` depends only on the first `i` challenges. -/
lemma trace_congr (ω ω' : ∀ i, Ch i) :
    ∀ j, (∀ k : Fin ν, (k : ℕ) < j → ω k = ω' k) → trace P x ω j = trace P x ω' j
  | 0, _ => rfl
  | j + 1, h => by
    have ih := trace_congr ω ω' j (fun k hk => h k (by omega))
    by_cases hj : j < ν
    · simp only [trace, hj, dif_pos, ih, h ⟨j, hj⟩ (by simp)]
    · simp only [trace, hj, dif_neg, not_false_eq_true, ih]

/-- The message `m_{i+1}` depends only on the challenges of rounds `< i`. -/
lemma msg_congr (ω ω' : ∀ i, Ch i) (i : Fin ν) (h : ∀ k : Fin ν, k < i → ω k = ω' k) :
    msg P x ω i = msg P x ω' i := by
  unfold msg; rw [trace_congr P x ω ω' i (fun k hk => h k hk)]

lemma trace_update (ω : ∀ i, Ch i) (i : Fin ν) (c : Ch i) :
    trace P x (Function.update ω i c) i = trace P x ω i :=
  trace_congr P x _ _ i (fun _ hk => Function.update_of_ne (Fin.ne_of_lt hk) _ _)

lemma msg_update (ω : ∀ i, Ch i) (i : Fin ν) (c : Ch i) :
    msg P x (Function.update ω i c) i = msg P x ω i :=
  msg_congr P x _ _ i (fun _ hk => Function.update_of_ne (Fin.ne_of_lt hk) _ _)

variable [∀ i, Fintype (Ch i)]

/-- Acceptance probability `Pr_Ω[V accepts τ_ν]` of a deterministic prover on instance `x`. -/
noncomputable def accProb (V : X → Transcript Ch M → Prop) (P : Prover Ch X M) (x : X) : ℚ :=
  prob (fun ω : (∀ i, Ch i) => V x (trace P x ω ν))

/-- The language `L_R = {x | ∃ w, (x,w) ∈ R}` of a relation (§3.1). -/
def Lang (R : X → W → Prop) (x : X) : Prop := ∃ w, R x w

/-- **Definition 3.5 (completeness).** The honest prover `Phon`, which also receives the
witness, makes the verifier accept with probability `1` on every `(x,w) ∈ R`. -/
def Complete (V : X → Transcript Ch M → Prop) (R : X → W → Prop)
    (Phon : X → W → Transcript Ch M → M) : Prop :=
  ∀ x w, R x w → accProb V (fun x' τ => Phon x' w τ) x = 1

/-- **Definition 3.5 (soundness error).** For `x ∉ L_R` and every deterministic prover,
the verifier accepts with probability at most `ε`. -/
def SoundnessError (V : X → Transcript Ch M → Prop) (R : X → W → Prop) (ε : ℚ) : Prop :=
  ∀ x, ¬ Lang R x → ∀ P : Prover Ch X M, accProb V P x ≤ ε

/-- **Definition 3.6 (round-by-round soundness), with a given doomed set `D`.**
`D x τ` means that the partial transcript `(x, τ)` is doomed.
1. `x ∉ L_R` ⇒ the empty transcript is doomed;
2. for a doomed partial transcript of `i` rounds and every message `m`,
   `Pr_{c ← Chᵢ}[(τ, m, c) ∉ D] ≤ εᵢ`;
3. `V` rejects every doomed full transcript. -/
def IsRBRSoundWith (V : X → Transcript Ch M → Prop) (R : X → W → Prop) (ε : Fin ν → ℚ)
    (D : X → Transcript Ch M → Prop) : Prop :=
  (∀ x, ¬ Lang R x → D x []) ∧
  (∀ x (i : Fin ν) (τ : Transcript Ch M), IsPartial τ i → D x τ → ∀ m : M,
      prob (fun c : Ch i => ¬ D x (τ ++ [(m, ⟨i, c⟩)])) ≤ ε i) ∧
  (∀ x τ, IsPartial τ ν → D x τ → ¬ V x τ)

/-- **Definition 3.6 (round-by-round soundness error `(ε₁,…,ε_ν)`).** -/
def RBRSound (V : X → Transcript Ch M → Prop) (R : X → W → Prop) (ε : Fin ν → ℚ) : Prop :=
  ∃ D, IsRBRSoundWith V R ε D

/-- **Definition 3.7 (round-by-round knowledge soundness), with given doomed set `D` and
extractor `Ext`.** The extractor is an arbitrary function of (instance, partial transcript,
next message); its running time is not modelled.
1. the empty transcript is doomed for every instance;
2. for a doomed partial transcript of `i` rounds and a message `m`, if
   `Pr_{c ← Chᵢ}[(τ, m, c) ∉ D] > εᵢ` then `(x, Ext(τ, m)) ∈ R`;
3. `V` rejects every doomed full transcript. -/
def IsRBRKnowledgeWith (V : X → Transcript Ch M → Prop) (R : X → W → Prop) (ε : Fin ν → ℚ)
    (D : X → Transcript Ch M → Prop) (Ext : X → Transcript Ch M → M → W) : Prop :=
  (∀ x, D x []) ∧
  (∀ x (i : Fin ν) (τ : Transcript Ch M), IsPartial τ i → D x τ → ∀ m : M,
      ε i < prob (fun c : Ch i => ¬ D x (τ ++ [(m, ⟨i, c⟩)])) → R x (Ext x τ m)) ∧
  (∀ x τ, IsPartial τ ν → D x τ → ¬ V x τ)

/-- **Definition 3.7 (round-by-round knowledge soundness with error `(ε₁,…,ε_ν)`).** -/
def RBRKnowledge (V : X → Transcript Ch M → Prop) (R : X → W → Prop) (ε : Fin ν → ℚ) : Prop :=
  ∃ D Ext, IsRBRKnowledgeWith V R ε D Ext

/-- First exit from a predicate on `ℕ`. -/
lemma exists_first_exit (p : ℕ → Prop) : ∀ n, p 0 → ¬ p n → ∃ i < n, p i ∧ ¬ p (i + 1)
  | 0, h0, hn => absurd h0 hn
  | n + 1, h0, hn => by
    by_cases h : p n
    · exact ⟨n, Nat.lt_succ_self n, h, hn⟩
    · obtain ⟨i, hi, h1, h2⟩ := exists_first_exit p n h0 h
      exact ⟨i, by omega, h1, h2⟩

variable [∀ i, Nonempty (Ch i)]

/-- Common core of Lemma 3.8. `D` is the doomed set at the fixed instance `x`; `B i τ m` is an
"escape" condition (in part 2, extraction succeeds) outside of which a doomed transcript stays
doomed except with probability `εᵢ`. -/
theorem accProb_le_core (V : X → Transcript Ch M → Prop) (ε : Fin ν → ℚ) (hε : ∀ i, 0 ≤ ε i)
    (D : Transcript Ch M → Prop) (B : (i : Fin ν) → Transcript Ch M → M → Prop)
    (h0 : D [])
    (h2 : ∀ (i : Fin ν) (τ : Transcript Ch M), IsPartial τ i → D τ → ∀ m : M, ¬ B i τ m →
      prob (fun c : Ch i => ¬ D (τ ++ [(m, ⟨i, c⟩)])) ≤ ε i)
    (h3 : ∀ τ, IsPartial τ ν → D τ → ¬ V x τ) :
    accProb V P x ≤ ∑ i, ε i +
      prob (fun ω : (∀ i, Ch i) => ∃ i : Fin ν, D (trace P x ω i) ∧
        B i (trace P x ω i) (msg P x ω i)) := by
  classical
  -- `Eᵢ`: doomed before round `i`, no escape, not doomed after round `i`.
  let E : Fin ν → (∀ i, Ch i) → Prop := fun i ω =>
    D (trace P x ω i) ∧ ¬ B i (trace P x ω i) (msg P x ω i) ∧
      ¬ D (trace P x ω i ++ [(msg P x ω i, ⟨i, ω i⟩)])
  have hacc : ∀ ω : (∀ i, Ch i), V x (trace P x ω ν) →
      (∃ i, E i ω) ∨ ∃ i : Fin ν, D (trace P x ω i) ∧ B i (trace P x ω i) (msg P x ω i) := by
    intro ω hV
    have hnD : ¬ D (trace P x ω ν) := fun hD => h3 _ (isPartial_trace P x ω ν le_rfl) hD hV
    obtain ⟨i, hi, hDi, hnDi⟩ :=
      exists_first_exit (fun j => D (trace P x ω j)) ν h0 hnD
    have hs := trace_succ P x ω ⟨i, hi⟩
    simp only at hs
    rw [hs] at hnDi
    by_cases hB : B ⟨i, hi⟩ (trace P x ω i) (msg P x ω ⟨i, hi⟩)
    · exact Or.inr ⟨⟨i, hi⟩, hDi, hB⟩
    · exact Or.inl ⟨⟨i, hi⟩, hDi, hB, hnDi⟩
  have hseq : prob (fun ω => ∃ i, E i ω) ≤ ∑ i, ε i := by
    have := sequential_challenges E (fun i => ε i * Fintype.card (Ch i)) ?_
    · refine this.trans (le_of_eq (sum_congr rfl fun i _ => ?_))
      have : (Fintype.card (Ch i) : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_pos.ne'
      exact mul_div_cancel_right₀ _ this
    · intro i ω
      have hE : ∀ c, E i (Function.update ω i c) ↔
          (D (trace P x ω i) ∧ ¬ B i (trace P x ω i) (msg P x ω i)) ∧
            ¬ D (trace P x ω i ++ [(msg P x ω i, ⟨i, c⟩)]) := by
        intro c
        simp only [E, trace_update, msg_update, Function.update_self, and_assoc]
      simp_rw [hE]
      by_cases hDB : D (trace P x ω i) ∧ ¬ B i (trace P x ω i) (msg P x ω i)
      · simp only [hDB, true_and, not_false_eq_true]
        have := h2 i _ (isPartial_trace P x ω i i.isLt.le) hDB.1 _ hDB.2
        rw [prob_def] at this
        have hc : (0 : ℚ) < Fintype.card (Ch i) := by exact_mod_cast Fintype.card_pos
        rwa [div_le_iff₀ hc] at this
      · simp only [hDB, false_and, filter_false, card_empty, Nat.cast_zero]
        exact mul_nonneg (hε i) (by positivity)
  calc accProb V P x
      ≤ prob (fun ω => (∃ i, E i ω) ∨ ∃ i : Fin ν, D (trace P x ω i) ∧
          B i (trace P x ω i) (msg P x ω i)) := prob_mono hacc
    _ ≤ _ := prob_or_le _ _
    _ ≤ _ := by gcongr

/-- **Lemma 3.8(1) (round-by-round soundness implies soundness).** With nonnegative errors,
round-by-round soundness error `(εᵢ)` implies soundness error `∑ εᵢ` against every
deterministic prover. (Nonnegativity of the `εᵢ` is implicit in the paper; it is needed.) -/
theorem rbr_soundness_overall (V : X → Transcript Ch M → Prop) (R : X → W → Prop)
    (ε : Fin ν → ℚ) (hε : ∀ i, 0 ≤ ε i) (h : RBRSound V R ε) :
    SoundnessError V R (∑ i, ε i) := by
  obtain ⟨D, h1, h2, h3⟩ := h
  intro x hx P
  have := accProb_le_core P x V ε hε (D x) (fun _ _ _ => False) (h1 x hx)
    (fun i τ hτ hD m _ => h2 x i τ hτ hD m) (h3 x)
  simpa [prob_false] using this

/-- **Lemma 3.8(2) (round-by-round knowledge soundness, overall bound).**
`Pr[V accepts] ≤ ∑ εᵢ + Pr[∃ i, τᵢ ∈ D ∧ (x, Ext(τᵢ, mᵢ₊₁)) ∈ R]`. -/
theorem rbr_knowledge_overall (V : X → Transcript Ch M → Prop) (R : X → W → Prop)
    (ε : Fin ν → ℚ) (hε : ∀ i, 0 ≤ ε i) (D : X → Transcript Ch M → Prop)
    (Ext : X → Transcript Ch M → M → W) (h : IsRBRKnowledgeWith V R ε D Ext) :
    accProb V P x ≤ ∑ i, ε i +
      prob (fun ω : (∀ i, Ch i) => ∃ i : Fin ν, D x (trace P x ω i) ∧
        R x (Ext x (trace P x ω i) (msg P x ω i))) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine accProb_le_core P x V ε hε (D x) (fun i τ m => R x (Ext x τ m)) (h1 x) ?_ (h3 x)
  intro i τ hτ hD m hR
  by_contra hlt
  exact hR (h2 x i τ hτ hD m (lt_of_not_ge hlt))

/-- **Lemma 3.8(2), "in particular".** If `V` accepts with probability `> ∑ εᵢ`, there are a
round `i` and challenges such that `τᵢ` is doomed and `Ext(τᵢ, mᵢ₊₁)` is a witness for `x`. -/
theorem rbr_knowledge_extract (V : X → Transcript Ch M → Prop) (R : X → W → Prop)
    (ε : Fin ν → ℚ) (hε : ∀ i, 0 ≤ ε i) (D : X → Transcript Ch M → Prop)
    (Ext : X → Transcript Ch M → M → W) (h : IsRBRKnowledgeWith V R ε D Ext)
    (hacc : ∑ i, ε i < accProb V P x) :
    ∃ (i : Fin ν) (ω : ∀ i, Ch i), D x (trace P x ω i) ∧
      R x (Ext x (trace P x ω i) (msg P x ω i)) := by
  have := rbr_knowledge_overall P x V R ε hε D Ext h
  obtain ⟨ω, i, hi⟩ := exists_of_prob_pos (show 0 < prob _ by linarith)
  exact ⟨i, ω, hi⟩

omit [∀ i, Nonempty (Ch i)] in
/-- **Lemma 3.4 (randomised provers), IOP form.** A randomised prover is a finitely supported
distribution `w` on a finite family `Ps` of deterministic provers; its probability of producing
a full transcript in `E` is the `w`-average of those of the deterministic provers. If every
deterministic prover has probability `≤ ε`, so does every randomised prover. -/
theorem randomised_prover_le {ι : Type*} (s : Finset ι) (w : ι → ℚ) (Ps : ι → Prover Ch X M)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hsum : ∑ i ∈ s, w i = 1) (E : Transcript Ch M → Prop) (ε : ℚ)
    (h : ∀ P : Prover Ch X M, prob (fun ω : (∀ i, Ch i) => E (trace P x ω ν)) ≤ ε) :
    ∑ i ∈ s, w i * prob (fun ω : (∀ i, Ch i) => E (trace (Ps i) x ω ν)) ≤ ε :=
  avg_le_of_forall_le s w _ hw hsum ε (fun i _ => h (Ps i))

end IOP

/-! ### §3.3 The sumcheck protocol (Lemma 3.9)

Modelling.  `K` is a finite field (the paper's `𝔽`), `F ∈ K[x₁,…,xₙ]` is an `MvPolynomial`
with `degreeOf k F ≤ 2` for every variable, rounds are `j : Fin n` (0-based) and the challenge
vector is `r : Fin n → K`.  The honest round polynomial is defined as in the paper,
`s*_j(X) = ∑_{b} F(r_{<j}, X, b_{>j})` over Boolean suffixes `b`, as an element of `K[X]`
(Boolean suffixes are represented by `b : Fin n → Bool` whose entries of index `≤ j` are `false`).
A prover strategy is a family `s j : (Fin n → K) → K[X]` with `s j r` depending only on
`r_{<j}` and `natDegree (s j r) ≤ 2` (messages in `K[X]_{<3}`); `msg_congr` shows that every
IOP prover yields such a family (`sumcheck_sound_iop`).  Acceptance is stated directly on
messages and challenges (`SumcheckAccepts`), with `v₀` the claimed sum and `vⱼ = sⱼ(rⱼ)`. -/

section Sumcheck

open Polynomial

variable {K : Type*} [Field K] {n : ℕ}

/-- The point `(r_{<j}, b_{≥j})`. -/
def prePt (j : ℕ) (r : Fin n → K) (b : Fin n → Bool) : Fin n → K :=
  fun k => if (k : ℕ) < j then r k else bval (b k)

/-- The point `(r_{<j}, a, b_{>j})`. -/
def mixPt (j : Fin n) (r : Fin n → K) (a : K) (b : Fin n → Bool) : Fin n → K :=
  fun k => if k < j then r k else if k = j then a else bval (b k)

/-- Boolean vectors vanishing below index `j`: they encode the Boolean suffixes
`b ∈ {0,1}^{n-j}` of the paper. -/
def zeroBelow (j : ℕ) : Finset (Fin n → Bool) :=
  univ.filter fun b => ∀ k : Fin n, (k : ℕ) < j → b k = false

/-- `v*_j = ∑_{b ∈ {0,1}^{n-j}} F(r_{<j}, b)`; `v*_0` is the true sum and `v*_n = F(r)`. -/
def vstar (Fv : (Fin n → K) → K) (r : Fin n → K) (j : ℕ) : K :=
  ∑ b ∈ zeroBelow j, Fv (prePt j r b)

/-- The substitution `x_k ↦ r_k (k<j), x_j ↦ X, x_k ↦ b_k (k>j)`. -/
noncomputable def roundSubst (j : Fin n) (r : Fin n → K) (b : Fin n → Bool) : Fin n → K[X] :=
  fun k => if k < j then C (r k) else if k = j then X else C (bval (b k))

/-- **Honest round polynomial (§3.3):** `s*_j(X) = ∑_b F(r_{<j}, X, b)` over Boolean suffixes. -/
noncomputable def sstar (F : MvPolynomial (Fin n) K) (j : Fin n) (r : Fin n → K) : K[X] :=
  ∑ b ∈ zeroBelow ((j : ℕ) + 1), MvPolynomial.aeval (roundSubst j r b) F

/-- The true sum `∑_{b ∈ {0,1}^n} F(b)`. -/
noncomputable def trueSum (F : MvPolynomial (Fin n) K) : K :=
  ∑ b : Fin n → Bool, MvPolynomial.eval (pt b) F

lemma eval_aeval_eq (F : MvPolynomial (Fin n) K) (g : Fin n → K[X]) (a : K) :
    (MvPolynomial.aeval g F).eval a = MvPolynomial.eval (fun k => (g k).eval a) F := by
  induction F using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p k hp => simp [hp]

lemma eval_sstar (F : MvPolynomial (Fin n) K) (j : Fin n) (r : Fin n → K) (a : K) :
    (sstar F j r).eval a = ∑ b ∈ zeroBelow ((j : ℕ) + 1), MvPolynomial.eval (mixPt j r a b) F := by
  rw [sstar, eval_finset_sum]
  refine sum_congr rfl (fun b _ => ?_)
  rw [eval_aeval_eq]
  have : (fun k => (roundSubst j r b k).eval a) = mixPt j r a b := by
    funext k
    simp only [roundSubst, mixPt]
    split_ifs <;> simp
  rw [this]

/-- `s*_j` depends only on `r_{<j}`. -/
lemma sstar_congr (F : MvPolynomial (Fin n) K) (j : Fin n) (r r' : Fin n → K)
    (h : ∀ k, k < j → r k = r' k) : sstar F j r = sstar F j r' := by
  unfold sstar
  refine sum_congr rfl (fun b _ => ?_)
  congr 2
  funext k
  simp only [roundSubst]
  split_ifs with hk
  · rw [h k hk]
  · rfl
  · rfl

/-- Splitting the Boolean coordinate `j` of a suffix sum. -/
lemma sum_zeroBelow_split {R : Type*} [AddCommMonoid R] (j : ℕ) (hj : j < n)
    (G : (Fin n → Bool) → R) :
    ∑ b ∈ zeroBelow j, G b
      = ∑ b ∈ zeroBelow (j + 1), (G b + G (Function.update b ⟨j, hj⟩ true)) := by
  classical
  set jj : Fin n := ⟨j, hj⟩
  rw [sum_add_distrib, ← sum_filter_add_sum_filter_not (zeroBelow j) (fun b => b jj = false)]
  congr 1
  · refine sum_congr ?_ (fun _ _ => rfl)
    ext b
    simp only [zeroBelow, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩ k hk
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | hk
      · exact h1 k hk
      · have : k = jj := Fin.ext hk
        rw [this]; exact h2
    · intro h
      exact ⟨fun k hk => h k (by omega), h jj (by simp [jj])⟩
  · apply sum_nbij' (fun b => Function.update b jj false) (fun b => Function.update b jj true)
    · intro b hb
      simp only [zeroBelow, mem_filter, mem_univ, true_and] at hb ⊢
      intro k hk
      rw [Function.update_apply]
      split_ifs with hkj
      · rfl
      · exact hb.1 k (by
          rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | hk
          · exact hk
          · exact absurd (Fin.ext hk) hkj)
    · intro b hb
      simp only [zeroBelow, mem_filter, mem_univ, true_and] at hb ⊢
      refine ⟨fun k hk => ?_, by simp⟩
      rw [Function.update_of_ne (fun h => by rw [h] at hk; simp [jj] at hk)]
      exact hb k (by omega)
    · intro b hb
      simp only [zeroBelow, mem_filter, mem_univ, true_and] at hb
      rw [Function.update_idem]
      have : b jj = true := by simpa using hb.2
      rw [← this, Function.update_eq_self]
    · intro b hb
      simp only [zeroBelow, mem_filter, mem_univ, true_and] at hb
      rw [Function.update_idem]
      have : b jj = false := hb jj (by simp [jj])
      rw [← this, Function.update_eq_self]
    · intro b hb
      simp only [zeroBelow, mem_filter, mem_univ, true_and] at hb
      rw [Function.update_idem]
      have : b jj = true := by simpa using hb.2
      rw [← this, Function.update_eq_self]

/-- `s*_j(0) + s*_j(1) = v*_j`. -/
lemma sstar_zero_add_one (F : MvPolynomial (Fin n) K) (j : Fin n) (r : Fin n → K) :
    (sstar F j r).eval 0 + (sstar F j r).eval 1 = vstar (fun p => MvPolynomial.eval p F) r j := by
  classical
  rw [eval_sstar, eval_sstar, ← sum_add_distrib, vstar, sum_zeroBelow_split (j : ℕ) j.isLt]
  refine sum_congr rfl (fun b hb => ?_)
  simp only [zeroBelow, mem_filter, mem_univ, true_and] at hb
  have hbj : b j = false := hb j (by simp)
  have e0 : mixPt j r 0 b = prePt j r b := by
    funext k
    simp only [prePt, mixPt]
    by_cases h1 : k < j
    · simp [h1, Fin.lt_def.mp h1]
    · have h1' : ¬ (k : ℕ) < j := fun h => h1 (Fin.lt_def.mpr h)
      by_cases h2 : k = j
      · subst h2; simp [hbj, bval]
      · simp [h1, h1', h2]
  have e1 : mixPt j r 1 b = prePt j r (Function.update b ⟨j, j.isLt⟩ true) := by
    funext k
    simp only [prePt, mixPt, Function.update_apply]
    by_cases h1 : k < j
    · simp [h1, Fin.lt_def.mp h1]
    · have h1' : ¬ (k : ℕ) < j := fun h => h1 (Fin.lt_def.mpr h)
      by_cases h2 : k = j
      · subst h2; simp [bval]
      · have h2' : k ≠ ⟨j, j.isLt⟩ := h2
        simp [h1, h1', h2]
  rw [e0, e1]

/-- `s*_j(r_j) = v*_{j+1}`. -/
lemma sstar_eval_r (F : MvPolynomial (Fin n) K) (j : Fin n) (r : Fin n → K) :
    (sstar F j r).eval (r j) = vstar (fun p => MvPolynomial.eval p F) r ((j : ℕ) + 1) := by
  rw [eval_sstar, vstar]
  refine sum_congr rfl (fun b _ => ?_)
  have e : mixPt j r (r j) b = prePt ((j : ℕ) + 1) r b := by
    funext k
    simp only [prePt, mixPt]
    by_cases h1 : k < j
    · simp [h1, show (k : ℕ) < j + 1 by have := Fin.lt_def.mp h1; omega]
    · have h1' : ¬ (k : ℕ) < j := fun h => h1 (Fin.lt_def.mpr h)
      by_cases h2 : k = j
      · subst h2; simp
      · have h3 : ¬ (k : ℕ) < j + 1 := fun h => h2 (Fin.ext (by omega))
        simp [h1, h2, h3]
  rw [e]

lemma vstar_zero (Fv : (Fin n → K) → K) (r : Fin n → K) :
    vstar Fv r 0 = ∑ b : Fin n → Bool, Fv (pt b) := by
  have : ∀ b : Fin n → Bool, prePt 0 r b = pt b := fun b => by
    funext k; simp [prePt, pt]
  simp [vstar, zeroBelow, this]

lemma vstar_n (Fv : (Fin n → K) → K) (r : Fin n → K) :
    vstar Fv r n = Fv r := by
  have : zeroBelow (n := n) n = {fun _ => false} := by
    ext b
    simp only [zeroBelow, mem_filter, mem_univ, true_and, mem_singleton]
    exact ⟨fun h => funext fun k => h k k.isLt, fun h k _ => by rw [h]⟩
  rw [vstar, this, sum_singleton]
  congr 1
  funext k
  simp [prePt, k.isLt]

/-- The honest round polynomial has degree `≤ 2` when `F` has degree `≤ 2` in each variable. -/
lemma natDegree_sstar_le (F : MvPolynomial (Fin n) K) (hF : ∀ k, F.degreeOf k ≤ 2)
    (j : Fin n) (r : Fin n → K) : (sstar F j r).natDegree ≤ 2 := by
  classical
  apply natDegree_sum_le_of_forall_le
  intro b _
  refine le_trans ?_ (hF j)
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq']
  apply natDegree_sum_le_of_forall_le
  intro d hd
  rw [Polynomial.algebraMap_eq]
  refine (natDegree_C_mul_le _ _).trans ?_
  refine (natDegree_prod_le _ _).trans ?_
  calc ∑ k, (roundSubst j r b k ^ d k).natDegree
      ≤ ∑ k, if k = j then d j else 0 := by
        refine sum_le_sum (fun k _ => ?_)
        refine natDegree_pow_le.trans ?_
        by_cases hkj : k = j
        · subst hkj; simp [roundSubst]
        · simp only [roundSubst, hkj, if_false]
          split_ifs <;> simp
    _ = d j := by simp
    _ ≤ F.degreeOf j := MvPolynomial.monomial_le_degreeOf j hd

/-- The verifier's running values `v₀` (claimed) and `v_{j+1} = s_j(r_j)`. -/
def vseq (v0 : K) (s : Fin n → K[X]) (r : Fin n → K) : ℕ → K
  | 0 => v0
  | j + 1 => if h : j < n then (s ⟨j, h⟩).eval (r ⟨j, h⟩) else 0

/-- The sumcheck verifier's decision (§3.3): `s_j(0) + s_j(1) = v_{j-1}` for every round and
`v_n = F(r)`. -/
def SumcheckAccepts (Fv : (Fin n → K) → K) (v0 : K) (s : Fin n → K[X]) (r : Fin n → K) : Prop :=
  (∀ j : Fin n, (s j).eval 0 + (s j).eval 1 = vseq v0 s r j) ∧ vseq v0 s r n = Fv r

/-- **Lemma 3.9 (sumcheck), completeness.** If `v₀` is the true sum, the honest prover is
accepted for every choice of challenges (hence with probability 1). -/
theorem sumcheck_complete (F : MvPolynomial (Fin n) K) (v0 : K) (hv : v0 = trueSum F)
    (r : Fin n → K) :
    SumcheckAccepts (fun p => MvPolynomial.eval p F) v0 (fun j => sstar F j r) r := by
  have key : ∀ j ≤ n, vseq v0 (fun j => sstar F j r) r j
      = vstar (fun p => MvPolynomial.eval p F) r j := by
    intro j hj
    cases j with
    | zero => simp [vseq, hv, trueSum, vstar_zero]
    | succ j =>
      have hj' : j < n := by omega
      simp only [vseq, hj', dif_pos]
      exact sstar_eval_r F ⟨j, hj'⟩ r
  refine ⟨fun j => ?_, ?_⟩
  · rw [key j j.isLt.le, sstar_zero_add_one]
  · rw [key n le_rfl, vstar_n]

/-- **Lemma 3.9 (sumcheck), "more precisely".** If `v₀` is not the true sum and the verifier
accepts messages `s` on challenges `r`, then some round `j` has `s_j ≠ s*_j` and
`s_j(r_j) = s*_j(r_j)`. (No degree assumption is needed here.) -/
theorem sumcheck_sound_core (F : MvPolynomial (Fin n) K) (v0 : K) (hv : v0 ≠ trueSum F)
    (s : Fin n → K[X]) (r : Fin n → K)
    (hacc : SumcheckAccepts (fun p => MvPolynomial.eval p F) v0 s r) :
    ∃ j : Fin n, s j ≠ sstar F j r ∧ (s j).eval (r j) = (sstar F j r).eval (r j) := by
  by_contra hne
  push_neg at hne
  have key : ∀ j ≤ n, vseq v0 s r j ≠ vstar (fun p => MvPolynomial.eval p F) r j := by
    intro j hj
    induction j with
    | zero => simpa [vseq, vstar_zero, trueSum] using hv
    | succ j ih =>
      have hj' : j < n := by omega
      have ih := ih (by omega)
      have h1 := hacc.1 ⟨j, hj'⟩
      have hsne : s ⟨j, hj'⟩ ≠ sstar F ⟨j, hj'⟩ r := by
        intro heq
        apply ih
        rw [← h1, heq, sstar_zero_add_one]
      simp only [vseq, hj', dif_pos]
      rw [← sstar_eval_r F ⟨j, hj'⟩ r]
      exact hne _ hsne
  exact key n le_rfl (by rw [hacc.2, vstar_n])

/-- **Lemma 2.1 (root counting), as used in Lemma 3.9:** two distinct polynomials of degree
`≤ 2` agree on at most `2` points. -/
lemma card_agree_le_two [Fintype K] [DecidableEq K] (p q : K[X]) (hpq : p ≠ q)
    (hp : p.natDegree ≤ 2) (hq : q.natDegree ≤ 2) :
    (univ.filter fun c : K => p.eval c = q.eval c).card ≤ 2 := by
  have hne : p - q ≠ 0 := sub_ne_zero.mpr hpq
  calc (univ.filter fun c : K => p.eval c = q.eval c).card
      ≤ (p - q).roots.toFinset.card := by
        apply card_le_card
        intro c hc
        simp only [mem_filter, mem_univ, true_and] at hc
        simp [Multiset.mem_toFinset, mem_roots hne, IsRoot, hc]
    _ ≤ Multiset.card (p - q).roots := Multiset.toFinset_card_le _
    _ ≤ (p - q).natDegree := card_roots' _
    _ ≤ max p.natDegree q.natDegree := natDegree_sub_le _ _
    _ ≤ 2 := max_le hp hq

/-- **Lemma 3.9 (sumcheck), soundness bound.** If the claimed sum `v₀` is wrong, every
deterministic prover strategy (round-`j` message a function of `r_{<j}`, of degree `≤ 2`)
is accepted with probability at most `2n/|K|` over uniform `r ∈ K^n`. -/
theorem sumcheck_sound [Fintype K] [DecidableEq K] (F : MvPolynomial (Fin n) K)
    (hF : ∀ k, F.degreeOf k ≤ 2) (v0 : K) (hv : v0 ≠ trueSum F)
    (s : Fin n → (Fin n → K) → K[X])
    (hcausal : ∀ j r r', (∀ k, k < j → r k = r' k) → s j r = s j r')
    (hdeg : ∀ j r, (s j r).natDegree ≤ 2) :
    prob (fun r : Fin n → K =>
        SumcheckAccepts (fun p => MvPolynomial.eval p F) v0 (fun j => s j r) r)
      ≤ 2 * n / Fintype.card K := by
  classical
  let E : Fin n → (Fin n → K) → Prop := fun j r =>
    s j r ≠ sstar F j r ∧ (s j r).eval (r j) = (sstar F j r).eval (r j)
  have h1 := sequential_challenges (Ch := fun _ : Fin n => K) E (fun _ => 2) ?_
  · calc _ ≤ prob (fun r => ∃ j, E j r) :=
          prob_mono (fun r hr => sumcheck_sound_core F v0 hv _ r hr)
      _ ≤ ∑ _j : Fin n, (2 : ℚ) / Fintype.card K := h1
      _ = 2 * n / Fintype.card K := by simp [mul_div_assoc, mul_comm]
  · intro j r
    have hupd : ∀ c : K, ∀ k, k < j → Function.update r j c k = r k :=
      fun c k hk => Function.update_of_ne (ne_of_lt hk) _ _
    have hE : ∀ c : K, E j (Function.update r j c) ↔
        (s j r ≠ sstar F j r ∧ (s j r).eval c = (sstar F j r).eval c) := by
      intro c
      simp only [E, hcausal j (Function.update r j c) r (hupd c),
        sstar_congr F j (Function.update r j c) r (hupd c), Function.update_self]
    simp_rw [hE]
    by_cases hne : s j r ≠ sstar F j r
    · simp only [hne, ne_eq, not_false_eq_true, true_and]
      exact_mod_cast card_agree_le_two _ _ hne (hdeg j r) (natDegree_sstar_le F hF j r)
    · simp [hne]

/-- **Lemma 3.9 for IOP provers.** In the sumcheck IOP (`n` rounds, challenges in `K`,
messages in `K[X]`, instance = claimed sum `v₀`), every deterministic prover whose messages
have degree `≤ 2` is accepted with probability at most `2n/|K|` when `v₀` is wrong. -/
theorem sumcheck_sound_iop [Fintype K] [DecidableEq K] (F : MvPolynomial (Fin n) K)
    (hF : ∀ k, F.degreeOf k ≤ 2) (v0 : K) (hv : v0 ≠ trueSum F)
    (P : Prover (fun _ : Fin n => K) K K[X]) (hdeg : ∀ x τ, (P x τ).natDegree ≤ 2) :
    prob (fun r : Fin n → K =>
        SumcheckAccepts (fun p => MvPolynomial.eval p F) v0 (fun j => msg P v0 r j) r)
      ≤ 2 * n / Fintype.card K :=
  sumcheck_sound F hF v0 hv (fun j r => msg P v0 r j)
    (fun j r r' h => msg_congr P v0 r r' j h) (fun _ _ => hdeg _ _)

end Sumcheck

/-! ### §3.4 Evaluation binding (Lemma 3.12), abstract form

Instances are triples `(w, z, v)` (word, point, value); tables `Tab` are encoded by
`Enc : Tab → Word`; `dist : Word → Word → Δ` takes values in any type with `≤`; `ev f z` is the
evaluation `f̃(z)` (abstract; instantiated with the multilinear extension `mle` below). -/

section Binding

variable {ν : ℕ} {Ch : Fin ν → Type*} [∀ i, Fintype (Ch i)] [∀ i, Nonempty (Ch i)] {M : Type*}
variable {Word Pt Val Tab Δ : Type*} [LE Δ]

/-- The relation `R^δ_eval = {((w; z, v), f) | dist(w, Enc f) ≤ δ ∧ f̃(z) = v}` (§3.4). -/
def evalRel (Enc : Tab → Word) (dist : Word → Word → Δ) (δ : Δ) (ev : Tab → Pt → Val) :
    Word × Pt × Val → Tab → Prop :=
  fun x f => dist x.1 (Enc f) ≤ δ ∧ ev f x.2.1 = x.2.2

/-- Uniqueness property `eq:dist-unique` of §3.4: every word is within distance `δ` of the encoding of at
most one table. -/
def UniqueWithin (Enc : Tab → Word) (dist : Word → Word → Δ) (δ : Δ) : Prop :=
  ∀ w f f', dist w (Enc f) ≤ δ → dist w (Enc f') ≤ δ → f = f'

/-- **Definition 3.11 (evaluation binding).** For every word `w`, point `z` and values
`v ≠ v'`, it is not the case that deterministic provers are accepted on both `(w; z, v)` and
`(w; z, v')` with probability `> ε`. -/
def EvalBinding (V : Word × Pt × Val → Transcript Ch M → Prop) (ε : ℚ) : Prop :=
  ∀ (w : Word) (z : Pt) (v v' : Val), v ≠ v' →
    ¬ ((∃ P : Prover Ch (Word × Pt × Val) M, ε < accProb V P (w, z, v)) ∧
       (∃ P' : Prover Ch (Word × Pt × Val) M, ε < accProb V P' (w, z, v')))

/-- **Lemma 3.12 (round-by-round knowledge soundness implies binding).** If the evaluation
protocol is round-by-round knowledge sound for `R^δ_eval` with (nonnegative) error `(εᵢ)` and
the uniqueness property holds, it is `∑ εᵢ`-evaluation binding. -/
theorem rbr_knowledge_binding (Enc : Tab → Word) (dist : Word → Word → Δ) (δ : Δ)
    (ev : Tab → Pt → Val) (V : Word × Pt × Val → Transcript Ch M → Prop) (ε : Fin ν → ℚ)
    (hε : ∀ i, 0 ≤ ε i) (hK : RBRKnowledge V (evalRel Enc dist δ ev) ε)
    (hU : UniqueWithin Enc dist δ) :
    EvalBinding V (∑ i, ε i) := by
  obtain ⟨D, Ext, hK⟩ := hK
  rintro w z v v' hvv' ⟨⟨P, hP⟩, ⟨P', hP'⟩⟩
  obtain ⟨i, ω, -, hf⟩ := rbr_knowledge_extract P (w, z, v) V _ ε hε D Ext hK hP
  obtain ⟨i', ω', -, hf'⟩ := rbr_knowledge_extract P' (w, z, v') V _ ε hε D Ext hK hP'
  have heq := hU w _ _ hf.1 hf'.1
  apply hvv'
  have h1 := hf.2
  have h2 := hf'.2
  simp only at h1 h2
  rw [← h1, ← h2, heq]

/-- Lemma 3.12 for multilinear evaluation claims: tables `Table K n`, evaluation `f̃(z)` by the
multilinear extension `mle` of `KBFold.Multilinear`. -/
theorem rbr_knowledge_binding_mle {K : Type*} [CommRing K] {n : ℕ}
    (Enc : Table K n → Word) (dist : Word → Word → Δ) (δ : Δ)
    (V : Word × (Fin n → K) × K → Transcript Ch M → Prop) (ε : Fin ν → ℚ)
    (hε : ∀ i, 0 ≤ ε i) (hK : RBRKnowledge V (evalRel Enc dist δ (fun f z => mle f z)) ε)
    (hU : UniqueWithin Enc dist δ) :
    EvalBinding V (∑ i, ε i) :=
  rbr_knowledge_binding Enc dist δ _ V ε hε hK hU

end Binding

end KBFold
