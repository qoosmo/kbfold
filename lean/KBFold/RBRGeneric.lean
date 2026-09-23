/-
KBFold/RBRGeneric.lean
Theorem 7.19, "Consequently": `Π_eval` is round-by-round knowledge sound for `R^δ_eval`
(Definition 3.7, `IsRBRKnowledgeWith` of `KBFold/RoundByRound.lean`), and Remark 7.20:
evaluation binding follows by Lemma 3.12 (`rbr_knowledge_binding`).

`Π_eval` as a generic public-coin IOP (Definition 3.1 as modelled in `KBFold/RoundByRound.lean`):
* `ℓ + 1` rounds; challenge sets `ChE i = F` for `i < ℓ` and `ChE ℓ = L^κ` (`Fin κ → L`);
* one message type `MsgE = F[X]_{<3} × (∏_j F^{L_j}) × Table F m`: the round-`(i+1)` message
  carries the round polynomial `s_{i+1}` (first component), the oracle `w_i` (the level-`i`
  entry of the second component, read for `1 ≤ i ≤ ℓ-1`), and, in the last round, the final table
  `g` (third component); unused components are ignored;
* instances `x = (w₀, (zp, zs), v)`; the point is `z = catPt ℓ zp zs`;
* the verifier `VE` parses a full transcript and runs the checks of §6.2 (`FullAccepts`);
* the doomed set `DE` is Definition 7.16 on parsed transcripts; the extractor is `Ext`.
-/
import KBFold.RBR

set_option autoImplicit false

open Polynomial Finset

namespace KBFold

universe u

section Generic

variable {F : Type u} [Field F] {L : Subgroup Fˣ} {m : ℕ} (ℓ κ : ℕ)

/-- The challenge sets of `Π_eval`: `F` in rounds `1, …, ℓ` and `L^κ` in round `ℓ+1`. -/
def ChE (i : Fin (ℓ + 1)) : Type u := if (i : ℕ) < ℓ then F else (Fin κ → L)

instance [Fintype F] [DecidableEq F] [Fintype L] (i : Fin (ℓ + 1)) :
    Fintype (ChE (F := F) (L := L) ℓ κ i) := by
  unfold ChE; split <;> infer_instance

instance (i : Fin (ℓ + 1)) : Nonempty (ChE (F := F) (L := L) ℓ κ i) := by
  unfold ChE; split
  · exact ⟨(0 : F)⟩
  · exact ⟨fun _ => (1 : L)⟩

variable {ℓ κ}

/-- A challenge of round `i < ℓ` is a field element. -/
def chF {i : Fin (ℓ + 1)} (h : (i : ℕ) < ℓ) : ChE (F := F) (L := L) ℓ κ i ≃ F :=
  Equiv.cast (by simp [ChE, h])

/-- The challenge of round `ℓ+1` is a `κ`-tuple of query points. -/
def chQ {i : Fin (ℓ + 1)} (h : ¬ (i : ℕ) < ℓ) : ChE (F := F) (L := L) ℓ κ i ≃ (Fin κ → L) :=
  Equiv.cast (by simp [ChE, h])

variable (L m)

/-- The message type (see the header). -/
abbrev MsgE : Type u := degreeLT F 3 × ((j : ℕ) → lv L j → F) × Table F m

variable {L m}

/-- Transcript entries of `Π_eval`. -/
abbrev EntE (ℓ κ : ℕ) := Entry (ChE (F := F) (L := L) ℓ κ) (MsgE L m)

/-- The round polynomial of an entry. -/
def entS (e : EntE (F := F) (L := L) (m := m) ℓ κ) : F[X] := (e.1.1 : F[X])

/-- The field challenge of an entry (`0` for the last round). -/
def entR (e : EntE (F := F) (L := L) (m := m) ℓ κ) : F :=
  if h : (e.2.1 : ℕ) < ℓ then chF h e.2.2 else 0

/-- The query points of an entry (a default value for rounds `≤ ℓ`). -/
def entQ (e : EntE (F := F) (L := L) (m := m) ℓ κ) : Fin κ → L :=
  if h : (e.2.1 : ℕ) < ℓ then fun _ => 1 else chQ h e.2.2

/-- Parsing a list transcript into the data of `KBFold/RBR.lean`. -/
noncomputable def parse (τ : List (EntE (F := F) (L := L) (m := m) ℓ κ)) : PTrans F L where
  s i := (τ[i]?.map entS).getD 0
  w j := (τ[j]?.map (fun e => e.1.2.1 j)).getD 0
  r i := (τ[i]?.map entR).getD 0

/-- The final table (third component of the last message). -/
noncomputable def gOf (τ : List (EntE (F := F) (L := L) (m := m) ℓ κ)) : Table F m :=
  (τ[ℓ]?.map (fun e => e.1.2.2)).getD 0

/-- The query points (challenge of the last round). -/
def ξOf (τ : List (EntE (F := F) (L := L) (m := m) ℓ κ)) : Fin κ → L :=
  (τ[ℓ]?.map entQ).getD (fun _ => 1)

variable (ℓ κ) (δ : ℚ)

/-- Instances `(w₀, (zp, zs), v)`. -/
abbrev InstE (L : Subgroup Fˣ) (m : ℕ) := (L → F) × ((ℕ → F) × (Fin m → F)) × F

/-- The verifier of `Π_eval` on a full transcript. -/
def VE (x : InstE L m) (τ : List (EntE (F := F) (L := L) (m := m) ℓ κ)) : Prop :=
  FullAccepts ℓ x.1 x.2.1.1 x.2.1.2 x.2.2 (parse τ) (gOf τ) (ξOf τ)

/-- The relation `R^δ_eval` with `dist = Δ^fib₀` (§7.6), in the form `evalRel` of §3.4. -/
def RE : InstE L m → Table F (m + ℓ) → Prop :=
  evalRel (Enc L) fibDist δ (fun f (z : (ℕ → F) × (Fin m → F)) => mle f (catPt ℓ z.1 z.2))

/-- **Definition 7.16** on list transcripts: `τ_0` is doomed; `τ_j` (`1 ≤ j ≤ ℓ`) is doomed iff
not "not doomed"; a full transcript is doomed iff the verifier rejects it. -/
def DE (x : InstE L m) (τ : List (EntE (F := F) (L := L) (m := m) ℓ κ)) : Prop :=
  if τ.length = 0 then True
  else if τ.length ≤ ℓ then ¬ NotDoomed ℓ x.1 x.2.1.1 x.2.1.2 x.2.2 δ (parse τ) τ.length
  else ¬ VE ℓ κ x τ

/-- **Definition 7.16 (extractor)**, reading only the commitment `w₀` of the instance. -/
noncomputable def ExtE (x : InstE L m) (_τ : List (EntE (F := F) (L := L) (m := m) ℓ κ))
    (_msg : MsgE L m) : Table F (m + ℓ) :=
  Ext ℓ x.1 δ

/-- The round errors of Theorem 7.19: `ε_j = (M_j + 2)/|F|` for `j ∈ [1, ℓ]` and
`ε_{ℓ+1} = (1-δ)^κ`. -/
noncomputable def εE [Fintype F] (i : Fin (ℓ + 1)) : ℚ :=
  if (i : ℕ) < ℓ then ((Nat.card (lv L ((i : ℕ) + 1)) : ℚ) + 2) / Fintype.card F else (1 - δ) ^ κ

end Generic

/-! ### Congruence of `NotDoomed` -/

section Congr

variable {F : Type*} [Field F] {L : Subgroup Fˣ} {m ℓ : ℕ} {w0 : L → F} {zp : ℕ → F}
  {zs : Fin m → F} {v : F} {δ : ℚ}

/-- `τ_j` only depends on `s_i, r_i, w_i` for `i < j`. -/
theorem NotDoomed_congr {τ τ' : PTrans F L} {j : ℕ}
    (h : ∀ k < j, τ.s k = τ'.s k ∧ τ.r k = τ'.r k ∧ τ.w k = τ'.w k) :
    NotDoomed ℓ w0 zp zs v δ τ j ↔ NotDoomed ℓ w0 zp zs v δ τ' j := by
  have hvv : ∀ i ≤ j, vvT v τ i = vvT v τ' i := by
    intro i hi
    cases i with
    | zero => rfl
    | succ i => simp only [vvT, (h i (by omega)).1, (h i (by omega)).2.1]
  have hWd : ∀ i < j, Wd w0 τ i = Wd w0 τ' i := by
    intro i hi
    cases i with
    | zero => rfl
    | succ i => simp only [Wd, (h (i + 1) hi).2.2]
  have hwhat : ∀ i < j, what w0 τ i = what w0 τ' i := by
    intro i hi
    simp only [what, hWd i hi, (h i hi).2.1]
  have hWset : ∀ c, Wset w0 τ j c = Wset w0 τ' j c := by
    intro c
    cases j with
    | zero => rfl
    | succ k =>
      ext ξ
      simp only [Wset, Set.mem_setOf_eq]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨fun i hi => ?_, ?_⟩
        · rw [← hwhat i (by omega), ← hWd (i + 1) (by omega)]; exact h1 i hi
        · rw [← hwhat k (by omega)]; exact h2
      · rintro ⟨h1, h2⟩
        refine ⟨fun i hi => ?_, ?_⟩
        · rw [hwhat i (by omega), hWd (i + 1) (by omega)]; exact h1 i hi
        · rw [hwhat k (by omega)]; exact h2
  have hsig : ∀ c, sigmaJ ℓ zp zs τ j c = sigmaJ ℓ zp zs τ' j c := by
    intro c
    simp only [sigmaJ]
    congr 1
    refine prod_congr rfl (fun i hi => ?_)
    rw [(h i (by simpa using hi)).2.1]
  simp only [NotDoomed, SCT, dens, hWset, hsig, hvv j le_rfl]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i hi => ?_, h2⟩
    rw [← (h i hi).1, ← hvv i hi.le]; exact h1 i hi
  · rintro ⟨h1, h2⟩
    refine ⟨fun i hi => ?_, h2⟩
    rw [(h i hi).1, hvv i hi.le]; exact h1 i hi

end Congr

/-! ### Parsing lemmas -/

section Parse

variable {F : Type u} [Field F] {L : Subgroup Fˣ} {m ℓ κ : ℕ}

lemma parse_append_lt (τ : List (EntE (F := F) (L := L) (m := m) ℓ κ)) (e : EntE ℓ κ) {k : ℕ}
    (hk : k < τ.length) :
    (parse (τ ++ [e])).s k = (parse τ).s k ∧ (parse (τ ++ [e])).r k = (parse τ).r k ∧
      (parse (τ ++ [e])).w k = (parse τ).w k := by
  simp only [parse, List.getElem?_append_left hk, and_self]

lemma parse_append_len (τ : List (EntE (F := F) (L := L) (m := m) ℓ κ)) (e : EntE ℓ κ) :
    (parse (τ ++ [e])).s τ.length = entS e ∧ (parse (τ ++ [e])).r τ.length = entR e ∧
      (parse (τ ++ [e])).w τ.length = e.1.2.1 τ.length := by
  simp [parse]

lemma length_of_isPartial {τ : List (EntE (F := F) (L := L) (m := m) ℓ κ)} {i : ℕ}
    (h : IsPartial τ i) : τ.length = i := by
  have := congrArg List.length h
  simpa using this

/-- Uniform probability is invariant under an equivalence of finite types. -/
lemma prob_equiv {A B : Type*} [Fintype A] [Fintype B] (e : A ≃ B) (P : B → Prop) :
    prob (fun a => P (e a)) = prob P := by
  classical
  rw [prob_def, prob_def, Fintype.card_congr e]
  congr 2
  exact_mod_cast Finset.card_equiv e (fun a => by simp)

end Parse

/-! ### Theorem 7.19, "Consequently" -/

section Main

variable {F : Type u} [Field F] [Fintype F] [DecidableEq F] {L : Subgroup Fˣ} [Fintype L]
  {m ℓ : ℕ} (κ : ℕ) {δ : ℚ}

/-- **Theorem 7.19 ("Consequently")**: `Π_eval` is round-by-round knowledge sound for
`R^δ_eval` (Definition 3.7) with doomed set `DE`, extractor `ExtE` and errors
`ε_j = (M_j+2)/|F|` (`j ≤ ℓ`), `ε_{ℓ+1} = (1-δ)^κ`. -/
theorem rbr_knowledge {R : ℕ} (hL : IsSmoothDomain L (m + ℓ + R)) (hℓ : 1 ≤ ℓ) (hδ0 : 0 < δ)
    (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2) :
    IsRBRKnowledgeWith (VE (F := F) (L := L) (m := m) ℓ κ) (RE ℓ δ) (εE (L := L) ℓ κ δ)
      (DE ℓ κ δ) (ExtE ℓ κ δ) := by
  classical
  refine ⟨fun x => by simp [DE], ?_, ?_⟩
  · -- condition 2
    rintro ⟨w0, ⟨zp, zs⟩, v⟩ i τ hτ hD msg hε
    have hlen := length_of_isPartial hτ
    by_cases hi : (i : ℕ) < ℓ
    · -- rounds `1, …, ℓ`: items 1 and 2
      simp only [εE, if_pos hi] at hε
      -- the reference transcript with the challenge of round `i+1` as a free variable
      let c0 : ChE (F := F) (L := L) ℓ κ i := (chF (F := F) (L := L) (κ := κ) hi).symm 0
      let τr : PTrans F L := parse (τ ++ [((msg, ⟨i, c0⟩) : EntE (F := F) (L := L) (m := m) ℓ κ)])
      have hpar : ∀ c : ChE (F := F) (L := L) ℓ κ i,
          ¬ DE ℓ κ δ (w0, (zp, zs), v) (τ ++ [((msg, ⟨i, c⟩) : EntE (F := F) (L := L) (m := m) ℓ κ)]) ↔
            NotDoomed ℓ w0 zp zs v δ (τr.updR i (chF (κ := κ) hi c)) (i + 1) := by
        intro c
        have hl : (τ ++ [((msg, ⟨i, c⟩) : EntE (F := F) (L := L) (m := m) ℓ κ)]).length = i + 1 := by simp [hlen]
        simp only [DE, hl, Nat.add_one_ne_zero, if_false, show i.val + 1 ≤ ℓ by omega, if_true,
          not_not]
        apply NotDoomed_congr
        intro k hk
        rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
        · obtain ⟨a1, a2, a3⟩ := parse_append_lt τ ((msg, ⟨i, c⟩) : EntE (F := F) (L := L) (m := m) ℓ κ) (k := k) (by omega)
          obtain ⟨b1, b2, b3⟩ := parse_append_lt τ ((msg, ⟨i, c0⟩) : EntE (F := F) (L := L) (m := m) ℓ κ) (k := k) (by omega)
          refine ⟨?_, ?_, ?_⟩
          · rw [a1]; exact b1.symm
          · simp only [PTrans.updR, Function.update_of_ne (show k ≠ i by omega)]
            rw [a2]; exact b2.symm
          · rw [a3]; exact b3.symm
        · obtain ⟨a1, a2, a3⟩ := parse_append_len τ ((msg, ⟨i, c⟩) : EntE (F := F) (L := L) (m := m) ℓ κ)
          obtain ⟨b1, b2, b3⟩ := parse_append_len τ ((msg, ⟨i, c0⟩) : EntE (F := F) (L := L) (m := m) ℓ κ)
          rw [hlen] at a1 a2 a3 b1 b2 b3
          refine ⟨?_, ?_, ?_⟩
          · rw [a1]; exact b1.symm
          · simp only [PTrans.updR, Function.update_self]
            rw [a2]; simp [entR, hi]
          · rw [a3]; exact b3.symm
      have hprob : prob (fun c : ChE (F := F) (L := L) ℓ κ i =>
          ¬ DE ℓ κ δ (w0, (zp, zs), v) (τ ++ [((msg, ⟨i, c⟩) : EntE (F := F) (L := L) (m := m) ℓ κ)])) =
          prob (fun a : F => NotDoomed ℓ w0 zp zs v δ (τr.updR i a) (i + 1)) := by
        rw [← prob_equiv (chF (F := F) (L := L) (κ := κ) hi)]
        congr 1; funext c; exact propext (hpar c)
      rw [hprob] at hε
      have hdeg : (τr.s i).natDegree ≤ 2 := by
        have e := (parse_append_len τ ((msg, ⟨i, c0⟩) : EntE (F := F) (L := L) (m := m) ℓ κ)).1
        rw [hlen] at e
        show ((parse (τ ++ [((msg, ⟨i, c0⟩) : EntE (F := F) (L := L) (m := m) ℓ κ)])).s i).natDegree ≤ 2
        rw [e, entS]
        have := msg.1.2
        rw [mem_degreeLT] at this
        exact natDegree_le_of_degree_le (Order.le_of_lt_succ (by exact_mod_cast this))
      by_cases hi0 : (i : ℕ) = 0
      · -- round 1 (item 1)
        by_contra hnw
        have := rbr_round_one hL hℓ hδ0 hδ (w0 := w0) (zp := zp) (zs := zs) (v := v) hnw τr
          (by rw [← hi0]; exact hdeg)
        rw [hi0] at hε
        exact absurd hε (not_lt.2 this)
      · -- rounds `2, …, ℓ` (item 2)
        exfalso
        have hdoom : Doomed ℓ w0 zp zs v δ τr i := by
          right
          have hD' : ¬ NotDoomed ℓ w0 zp zs v δ (parse τ) i := by
            simp only [DE, hlen, hi0, if_false, show (i : ℕ) ≤ ℓ by omega, if_true] at hD
            exact hD
          rwa [NotDoomed_congr (fun k hk => by
            obtain ⟨a1, a2, a3⟩ := parse_append_lt τ ((msg, ⟨i, c0⟩) : EntE (F := F) (L := L) (m := m) ℓ κ) (k := k) (by omega)
            exact ⟨a1, a2, a3⟩)]
        have := rbr_round hL hδ0 hδ τr (by omega) hi hdoom hdeg
        exact absurd hε (not_lt.2 this)
    · -- round `ℓ + 1` (item 3)
      exfalso
      have hiℓ : (i : ℕ) = ℓ := by omega
      simp only [εE, if_neg hi] at hε
      have hD' : ¬ NotDoomed ℓ w0 zp zs v δ (parse τ) ℓ := by
        simp only [DE, hlen, hiℓ, show ℓ ≠ 0 by omega, if_false, le_refl, if_true] at hD
        exact hD
      let c0 : ChE (F := F) (L := L) ℓ κ i := (chQ (F := F) (L := L) (κ := κ) hi).symm (fun _ => 1)
      let τr : PTrans F L := parse (τ ++ [((msg, ⟨i, c0⟩) : EntE (F := F) (L := L) (m := m) ℓ κ)])
      have hpar : ∀ c : ChE (F := F) (L := L) ℓ κ i,
          ¬ DE ℓ κ δ (w0, (zp, zs), v) (τ ++ [((msg, ⟨i, c⟩) : EntE (F := F) (L := L) (m := m) ℓ κ)]) ↔
            FullAccepts ℓ w0 zp zs v τr msg.2.2 (chQ (F := F) (κ := κ) hi c) := by
        intro c
        have hl : (τ ++ [((msg, ⟨i, c⟩) : EntE (F := F) (L := L) (m := m) ℓ κ)]).length = ℓ + 1 := by simp [hlen, hiℓ]
        simp only [DE, hl, Nat.add_one_ne_zero, if_false, show ¬ (ℓ + 1 ≤ ℓ) by omega, not_not]
        have hparse : parse (τ ++ [((msg, ⟨i, c⟩) : EntE (F := F) (L := L) (m := m) ℓ κ)]) = τr := by
          simp only [τr, parse, PTrans.mk.injEq]
          refine ⟨?_, ?_, ?_⟩ <;> funext k <;> rcases lt_or_ge k τ.length with hk | hk
          · simp [List.getElem?_append_left hk]
          · rw [List.getElem?_append_right hk, List.getElem?_append_right hk]
            rcases Nat.eq_or_lt_of_le hk with h' | h'
            · rw [← h']; simp [entS]
            · simp [show k - τ.length ≠ 0 by omega]
          · simp [List.getElem?_append_left hk]
          · rw [List.getElem?_append_right hk, List.getElem?_append_right hk]
            rcases Nat.eq_or_lt_of_le hk with h' | h'
            · rw [← h']; simp
            · simp [show k - τ.length ≠ 0 by omega]
          · simp [List.getElem?_append_left hk]
          · rw [List.getElem?_append_right hk, List.getElem?_append_right hk]
            rcases Nat.eq_or_lt_of_le hk with h' | h'
            · rw [← h']; simp [entR, hi]
            · simp [show k - τ.length ≠ 0 by omega]
        have hlast : (τ ++ [((msg, ⟨i, c⟩) : EntE (F := F) (L := L) (m := m) ℓ κ)])[ℓ]? =
            some (msg, ⟨i, c⟩) := by
          rw [List.getElem?_append_right (by omega)]
          simp [show ℓ - τ.length = 0 by omega]
        have hg : gOf (τ ++ [((msg, ⟨i, c⟩) : EntE (F := F) (L := L) (m := m) ℓ κ)]) = msg.2.2 := by
          simp [gOf, hlast]
        have hξ : ξOf (τ ++ [((msg, ⟨i, c⟩) : EntE (F := F) (L := L) (m := m) ℓ κ)]) =
            chQ (κ := κ) hi c := by
          simp [ξOf, hlast, entQ, hi]
        simp only [VE, hparse, hg, hξ]
      have hprob : prob (fun c : ChE (F := F) (L := L) ℓ κ i =>
          ¬ DE ℓ κ δ (w0, (zp, zs), v) (τ ++ [((msg, ⟨i, c⟩) : EntE (F := F) (L := L) (m := m) ℓ κ)])) =
          prob (fun ξ : Fin κ → L => FullAccepts ℓ w0 zp zs v τr msg.2.2 ξ) := by
        rw [← prob_equiv (chQ (F := F) (L := L) (κ := κ) hi)]
        congr 1; funext c; exact propext (hpar c)
      rw [hprob] at hε
      have hdoom : Doomed ℓ w0 zp zs v δ τr ℓ := by
        right
        rwa [NotDoomed_congr (fun k hk => by
          obtain ⟨a1, a2, a3⟩ := parse_append_lt τ ((msg, ⟨i, c0⟩) : EntE (F := F) (L := L) (m := m) ℓ κ) (k := k) (by omega)
          exact ⟨a1, a2, a3⟩)]
      have := rbr_final hL hℓ hδ τr hdoom msg.2.2 κ
      exact absurd hε (not_lt.2 this)
  · -- condition 3
    rintro x τ hτ hD
    have hlen := length_of_isPartial hτ
    simp only [DE, hlen, Nat.add_one_ne_zero, if_false, show ¬ (ℓ + 1 ≤ ℓ) by omega] at hD
    exact hD

/-- **Theorem 7.19**, in the form of Definition 3.7 (`RBRKnowledge`). -/
theorem rbr_knowledge' {R : ℕ} (hL : IsSmoothDomain L (m + ℓ + R)) (hℓ : 1 ≤ ℓ) (hδ0 : 0 < δ)
    (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2) :
    RBRKnowledge (VE (F := F) (L := L) (m := m) ℓ κ) (RE ℓ δ) (εE (L := L) ℓ κ δ) :=
  ⟨_, _, rbr_knowledge κ hL hℓ hδ0 hδ⟩

omit [Fintype F] [DecidableEq F] [Fintype L] in
/-- Condition `eq:dist-unique` for `dist = Δ^fib₀` (§7.6, "Relation"): by Lemma 7.3 and the
injectivity of `Enc`. -/
theorem uniqueWithin_fib {R : ℕ} (hL : IsSmoothDomain L (m + ℓ + R)) (hℓ : 1 ≤ ℓ)
    (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2) :
    UniqueWithin (Enc L (n := m + ℓ) (F := F)) fibDist δ := by
  intro w f f' h1 h1'
  haveI := hL.finite
  have hd : 2 ^ (m + ℓ) ≤ Nat.card L := Nd_le_card hL (j := 0) (by omega)
  have hrate : rate L (2 ^ (m + ℓ)) = 1 / 2 ^ R := rate_lv hL (j := 0) (by omega)
  have hδ' : δ ≤ (1 - rate L (2 ^ (m + ℓ))) / 2 := by rw [hrate]; exact hδ
  have hneg : (-1 : Fˣ) ∈ L := hL.neg_one_mem (by omega)
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_smooth hL (by omega)
  exact Enc_injective hd (fib_unique hneg h2 hδ' w (Enc_mem_RS L f) (Enc_mem_RS L f') h1 h1')

/-- **Remark 7.20:** by Lemma 3.12, Theorem 7.19 implies that `Π_eval` (as a generic IOP) is
`ε`-evaluation binding (Definition 3.11) with `ε = ∑_{j=1}^{ℓ} (M_j+2)/|F| + (1-δ)^κ`. -/
theorem rbr_binding {R : ℕ} (hL : IsSmoothDomain L (m + ℓ + R)) (hℓ : 1 ≤ ℓ) (hδ0 : 0 < δ)
    (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2) :
    EvalBinding (VE (F := F) (L := L) (m := m) ℓ κ) (∑ i, εE (L := L) ℓ κ δ i) := by
  have hR : (0 : ℚ) < 1 / 2 ^ R := by positivity
  refine rbr_knowledge_binding (Enc L) fibDist δ _ _ (εE (L := L) ℓ κ δ) ?_
    (rbr_knowledge' κ hL hℓ hδ0 hδ) (uniqueWithin_fib hL hℓ hδ)
  intro i
  simp only [εE]
  split_ifs
  · positivity
  · exact pow_nonneg (by linarith) κ

end Main

end KBFold
