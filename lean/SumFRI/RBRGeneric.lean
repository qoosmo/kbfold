/-
SumFRI/RBRGeneric.lean
Theorem 6.20, "Consequently": `Π_eval` is round-by-round knowledge sound for `R^δ_eval`
(Definition 3.7, `IsRBRKnowledgeWith` of `KBFold/RoundByRound.lean`), and Remark 6.21:
evaluation binding follows by Lemma 3.12 (`rbr_knowledge_binding`).

The modelling is that of `KBFold/RBRGeneric.lean` (the challenge sets `ChE`, `chF`, `chQ` and
`prob_equiv` are reused), with one change: the round polynomial component of a message lies in
`F[X]_{<2}` (`cMsgE`).
* `ℓ + 1` rounds; challenge sets `ChE i = F` for `i < ℓ` and `ChE ℓ = L^κ`;
* message type `cMsgE = F[X]_{<2} × (∏_j F^{L_j}) × Table F m`: the round-`(i+1)` message carries
  the round polynomial `s_{i+1}`, the oracle `w_i` (read for `1 ≤ i ≤ ℓ-1`) and, in the last
  round, the final table `g`; unused components are ignored;
* instances `x = (w₀, (zp, zs), v)`; the point is `z = catPt ℓ zp zs`;
* the verifier `cVE` parses a full transcript and runs the checks of §5.2 (`cFullAccepts`);
* the doomed set `cDE` is Definition 6.17 on parsed transcripts; the extractor is `cExt`.
-/
import SumFRI.RBR
import KBFold.RBRGeneric

set_option autoImplicit false

open Polynomial Finset

namespace SumFRI

open KBFold

universe u

section Generic

variable {F : Type u} [Field F] {L : Subgroup Fˣ} {m : ℕ} {ℓ κ : ℕ}

variable (L m)

/-- The message type (see the header). -/
abbrev cMsgE : Type u := degreeLT F 2 × ((j : ℕ) → lv L j → F) × Table F m

variable {L m}

/-- Transcript entries of `Π_eval`. -/
abbrev cEntE (ℓ κ : ℕ) := Entry (ChE (F := F) (L := L) ℓ κ) (cMsgE L m)

/-- The round polynomial of an entry. -/
def centS (e : cEntE (F := F) (L := L) (m := m) ℓ κ) : F[X] := (e.1.1 : F[X])

/-- The field challenge of an entry (`0` for the last round). -/
def centR (e : cEntE (F := F) (L := L) (m := m) ℓ κ) : F :=
  if h : (e.2.1 : ℕ) < ℓ then chF h e.2.2 else 0

/-- The query points of an entry (a default value for rounds `≤ ℓ`). -/
def centQ (e : cEntE (F := F) (L := L) (m := m) ℓ κ) : Fin κ → L :=
  if h : (e.2.1 : ℕ) < ℓ then fun _ => 1 else chQ h e.2.2

/-- Parsing a list transcript into the data of `KBFold/RBR.lean`. -/
noncomputable def cparse (τ : List (cEntE (F := F) (L := L) (m := m) ℓ κ)) : PTrans F L where
  s i := (τ[i]?.map centS).getD 0
  w j := (τ[j]?.map (fun e => e.1.2.1 j)).getD 0
  r i := (τ[i]?.map centR).getD 0

/-- The final table (third component of the last message). -/
noncomputable def cgOf (τ : List (cEntE (F := F) (L := L) (m := m) ℓ κ)) : Table F m :=
  (τ[ℓ]?.map (fun e => e.1.2.2)).getD 0

/-- The query points (challenge of the last round). -/
def cξOf (τ : List (cEntE (F := F) (L := L) (m := m) ℓ κ)) : Fin κ → L :=
  (τ[ℓ]?.map centQ).getD (fun _ => 1)

variable (ℓ κ) (δ : ℚ)

/-- The verifier of `Π_eval` on a full transcript. -/
def cVE (x : InstE L m) (τ : List (cEntE (F := F) (L := L) (m := m) ℓ κ)) : Prop :=
  cFullAccepts ℓ x.1 x.2.1.1 x.2.1.2 x.2.2 (cparse τ) (cgOf τ) (cξOf τ)

/-- The relation `R^δ_eval` with `dist = Δ^fib₀` (§6.6), in the form `evalRel` of §3.4. -/
def cRE : InstE L m → Table F (m + ℓ) → Prop :=
  evalRel (cEnc L) fibDist δ (fun f (z : (ℕ → F) × (Fin m → F)) => cpoly f (catPt ℓ z.1 z.2))

/-- **Definition 6.17** on list transcripts: `τ_0` is doomed; `τ_j` (`1 ≤ j ≤ ℓ`) is doomed iff
not "not doomed"; a full transcript is doomed iff the verifier rejects it. -/
def cDE (x : InstE L m) (τ : List (cEntE (F := F) (L := L) (m := m) ℓ κ)) : Prop :=
  if τ.length = 0 then True
  else if τ.length ≤ ℓ then ¬ cNotDoomed ℓ x.1 x.2.1.1 x.2.1.2 x.2.2 δ (cparse τ) τ.length
  else ¬ cVE ℓ κ x τ

/-- **Definition 6.17 (extractor)**, reading only the commitment `w₀` of the instance. -/
noncomputable def cExtE (x : InstE L m) (_τ : List (cEntE (F := F) (L := L) (m := m) ℓ κ))
    (_msg : cMsgE L m) : Table F (m + ℓ) :=
  cExt ℓ x.1 δ

/-- The round errors of Theorem 6.20: `ε_j = (M_j + 1)/|F|` for `j ∈ [1, ℓ]` and
`ε_{ℓ+1} = (1-δ)^κ`. -/
noncomputable def cεE [Fintype F] (i : Fin (ℓ + 1)) : ℚ :=
  if (i : ℕ) < ℓ then ((Nat.card (lv L ((i : ℕ) + 1)) : ℚ) + 1) / Fintype.card F else (1 - δ) ^ κ

end Generic

/-! ### Congruence of `cNotDoomed` -/

section Congr

variable {F : Type*} [Field F] {L : Subgroup Fˣ} {m ℓ : ℕ} {w0 : L → F} {zp : ℕ → F}
  {zs : Fin m → F} {v : F} {δ : ℚ}

/-- `τ_j` only depends on `s_i, θ_i, w_i` for `i < j`. -/
theorem cNotDoomed_congr {τ τ' : PTrans F L} {j : ℕ}
    (h : ∀ k < j, τ.s k = τ'.s k ∧ τ.r k = τ'.r k ∧ τ.w k = τ'.w k) :
    cNotDoomed ℓ w0 zp zs v δ τ j ↔ cNotDoomed ℓ w0 zp zs v δ τ' j := by
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
  have hwhat : ∀ i < j, cwhat w0 τ i = cwhat w0 τ' i := by
    intro i hi
    simp only [cwhat, hWd i hi, (h i hi).2.1]
  have hWset : ∀ c, cWset w0 τ j c = cWset w0 τ' j c := by
    intro c
    cases j with
    | zero => rfl
    | succ k =>
      ext ξ
      simp only [cWset, Set.mem_setOf_eq]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨fun i hi => ?_, ?_⟩
        · rw [← hwhat i (by omega), ← hWd (i + 1) (by omega)]; exact h1 i hi
        · rw [← hwhat k (by omega)]; exact h2
      · rintro ⟨h1, h2⟩
        refine ⟨fun i hi => ?_, ?_⟩
        · rw [hwhat i (by omega), hWd (i + 1) (by omega)]; exact h1 i hi
        · rw [hwhat k (by omega)]; exact h2
  simp only [cNotDoomed, RestrT, cdens, hWset, hvv j le_rfl]
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

lemma cparse_append_lt (τ : List (cEntE (F := F) (L := L) (m := m) ℓ κ)) (e : cEntE ℓ κ) {k : ℕ}
    (hk : k < τ.length) :
    (cparse (τ ++ [e])).s k = (cparse τ).s k ∧ (cparse (τ ++ [e])).r k = (cparse τ).r k ∧
      (cparse (τ ++ [e])).w k = (cparse τ).w k := by
  simp only [cparse, List.getElem?_append_left hk, and_self]

lemma cparse_append_len (τ : List (cEntE (F := F) (L := L) (m := m) ℓ κ)) (e : cEntE ℓ κ) :
    (cparse (τ ++ [e])).s τ.length = centS e ∧ (cparse (τ ++ [e])).r τ.length = centR e ∧
      (cparse (τ ++ [e])).w τ.length = e.1.2.1 τ.length := by
  simp [cparse]

lemma clength_of_isPartial {τ : List (cEntE (F := F) (L := L) (m := m) ℓ κ)} {i : ℕ}
    (h : IsPartial τ i) : τ.length = i := by
  have := congrArg List.length h
  simpa using this

end Parse

/-! ### Theorem 6.20, "Consequently" -/

section Main

variable {F : Type u} [Field F] [Fintype F] [DecidableEq F] {L : Subgroup Fˣ} [Fintype L]
  {m ℓ : ℕ} (κ : ℕ) {δ : ℚ}

/-- **Theorem 6.20 ("Consequently")**: `Π_eval` is round-by-round knowledge sound for
`R^δ_eval` (Definition 3.7) with doomed set `cDE`, extractor `cExtE` and errors
`ε_j = (M_j+1)/|F|` (`j ≤ ℓ`), `ε_{ℓ+1} = (1-δ)^κ`. -/
theorem crbr_knowledge {R : ℕ} (hL : IsSmoothDomain L (m + ℓ + R)) (hℓ : 1 ≤ ℓ) (hδ0 : 0 < δ)
    (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2) :
    IsRBRKnowledgeWith (cVE (F := F) (L := L) (m := m) ℓ κ) (cRE ℓ δ) (cεE (L := L) ℓ κ δ)
      (cDE ℓ κ δ) (cExtE ℓ κ δ) := by
  classical
  refine ⟨fun x => by simp [cDE], ?_, ?_⟩
  · -- condition 2
    rintro ⟨w0, ⟨zp, zs⟩, v⟩ i τ hτ hD msg hε
    have hlen := clength_of_isPartial hτ
    by_cases hi : (i : ℕ) < ℓ
    · -- rounds `1, …, ℓ`: items 1 and 2
      simp only [cεE, if_pos hi] at hε
      -- the reference transcript with the challenge of round `i+1` as a free variable
      let c0 : ChE (F := F) (L := L) ℓ κ i := (chF (F := F) (L := L) (κ := κ) hi).symm 0
      let τr : PTrans F L := cparse (τ ++ [((msg, ⟨i, c0⟩) : cEntE (F := F) (L := L) (m := m) ℓ κ)])
      have hpar : ∀ c : ChE (F := F) (L := L) ℓ κ i,
          ¬ cDE ℓ κ δ (w0, (zp, zs), v) (τ ++ [((msg, ⟨i, c⟩) : cEntE (F := F) (L := L) (m := m) ℓ κ)]) ↔
            cNotDoomed ℓ w0 zp zs v δ (τr.updR i (chF (κ := κ) hi c)) (i + 1) := by
        intro c
        have hl : (τ ++ [((msg, ⟨i, c⟩) : cEntE (F := F) (L := L) (m := m) ℓ κ)]).length = i + 1 := by simp [hlen]
        simp only [cDE, hl, Nat.add_one_ne_zero, if_false, show i.val + 1 ≤ ℓ by omega, if_true,
          not_not]
        apply cNotDoomed_congr
        intro k hk
        rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
        · obtain ⟨a1, a2, a3⟩ := cparse_append_lt τ ((msg, ⟨i, c⟩) : cEntE (F := F) (L := L) (m := m) ℓ κ) (k := k) (by omega)
          obtain ⟨b1, b2, b3⟩ := cparse_append_lt τ ((msg, ⟨i, c0⟩) : cEntE (F := F) (L := L) (m := m) ℓ κ) (k := k) (by omega)
          refine ⟨?_, ?_, ?_⟩
          · rw [a1]; exact b1.symm
          · simp only [PTrans.updR, Function.update_of_ne (show k ≠ i by omega)]
            rw [a2]; exact b2.symm
          · rw [a3]; exact b3.symm
        · obtain ⟨a1, a2, a3⟩ := cparse_append_len τ ((msg, ⟨i, c⟩) : cEntE (F := F) (L := L) (m := m) ℓ κ)
          obtain ⟨b1, b2, b3⟩ := cparse_append_len τ ((msg, ⟨i, c0⟩) : cEntE (F := F) (L := L) (m := m) ℓ κ)
          rw [hlen] at a1 a2 a3 b1 b2 b3
          refine ⟨?_, ?_, ?_⟩
          · rw [a1]; exact b1.symm
          · simp only [PTrans.updR, Function.update_self]
            rw [a2]; simp [centR, hi]
          · rw [a3]; exact b3.symm
      have hprob : prob (fun c : ChE (F := F) (L := L) ℓ κ i =>
          ¬ cDE ℓ κ δ (w0, (zp, zs), v) (τ ++ [((msg, ⟨i, c⟩) : cEntE (F := F) (L := L) (m := m) ℓ κ)])) =
          prob (fun a : F => cNotDoomed ℓ w0 zp zs v δ (τr.updR i a) (i + 1)) := by
        rw [← prob_equiv (chF (F := F) (L := L) (κ := κ) hi)]
        congr 1; funext c; exact propext (hpar c)
      rw [hprob] at hε
      have hdeg : (τr.s i).natDegree ≤ 1 := by
        have e := (cparse_append_len τ ((msg, ⟨i, c0⟩) : cEntE (F := F) (L := L) (m := m) ℓ κ)).1
        rw [hlen] at e
        show ((cparse (τ ++ [((msg, ⟨i, c0⟩) : cEntE (F := F) (L := L) (m := m) ℓ κ)])).s i).natDegree ≤ 1
        rw [e, centS]
        have := msg.1.2
        rw [mem_degreeLT, degree_lt_iff_coeff_zero] at this
        exact natDegree_le_iff_coeff_eq_zero.2 (fun N hN => this N (by omega))
      by_cases hi0 : (i : ℕ) = 0
      · -- round 1 (item 1)
        by_contra hnw
        have := crbr_round_one hL hℓ hδ0 hδ (w0 := w0) (zp := zp) (zs := zs) (v := v) hnw τr
          (by rw [← hi0]; exact hdeg)
        rw [hi0] at hε
        exact absurd hε (not_lt.2 this)
      · -- rounds `2, …, ℓ` (item 2)
        exfalso
        have hdoom : cDoomed ℓ w0 zp zs v δ τr i := by
          right
          have hD' : ¬ cNotDoomed ℓ w0 zp zs v δ (cparse τ) i := by
            simp only [cDE, hlen, hi0, if_false, show (i : ℕ) ≤ ℓ by omega, if_true] at hD
            exact hD
          rwa [cNotDoomed_congr (fun k hk => by
            obtain ⟨a1, a2, a3⟩ := cparse_append_lt τ ((msg, ⟨i, c0⟩) : cEntE (F := F) (L := L) (m := m) ℓ κ) (k := k) (by omega)
            exact ⟨a1, a2, a3⟩)]
        have := crbr_round hL hδ0 hδ τr (by omega) hi hdoom hdeg
        exact absurd hε (not_lt.2 this)
    · -- round `ℓ + 1` (item 3)
      exfalso
      have hiℓ : (i : ℕ) = ℓ := by omega
      simp only [cεE, if_neg hi] at hε
      have hD' : ¬ cNotDoomed ℓ w0 zp zs v δ (cparse τ) ℓ := by
        simp only [cDE, hlen, hiℓ, show ℓ ≠ 0 by omega, if_false, le_refl, if_true] at hD
        exact hD
      let c0 : ChE (F := F) (L := L) ℓ κ i := (chQ (F := F) (L := L) (κ := κ) hi).symm (fun _ => 1)
      let τr : PTrans F L := cparse (τ ++ [((msg, ⟨i, c0⟩) : cEntE (F := F) (L := L) (m := m) ℓ κ)])
      have hpar : ∀ c : ChE (F := F) (L := L) ℓ κ i,
          ¬ cDE ℓ κ δ (w0, (zp, zs), v) (τ ++ [((msg, ⟨i, c⟩) : cEntE (F := F) (L := L) (m := m) ℓ κ)]) ↔
            cFullAccepts ℓ w0 zp zs v τr msg.2.2 (chQ (F := F) (κ := κ) hi c) := by
        intro c
        have hl : (τ ++ [((msg, ⟨i, c⟩) : cEntE (F := F) (L := L) (m := m) ℓ κ)]).length = ℓ + 1 := by simp [hlen, hiℓ]
        simp only [cDE, hl, Nat.add_one_ne_zero, if_false, show ¬ (ℓ + 1 ≤ ℓ) by omega, not_not]
        have hparse : cparse (τ ++ [((msg, ⟨i, c⟩) : cEntE (F := F) (L := L) (m := m) ℓ κ)]) = τr := by
          simp only [τr, cparse, PTrans.mk.injEq]
          refine ⟨?_, ?_, ?_⟩ <;> funext k <;> rcases lt_or_ge k τ.length with hk | hk
          · simp [List.getElem?_append_left hk]
          · rw [List.getElem?_append_right hk, List.getElem?_append_right hk]
            rcases Nat.eq_or_lt_of_le hk with h' | h'
            · rw [← h']; simp [centS]
            · simp [show k - τ.length ≠ 0 by omega]
          · simp [List.getElem?_append_left hk]
          · rw [List.getElem?_append_right hk, List.getElem?_append_right hk]
            rcases Nat.eq_or_lt_of_le hk with h' | h'
            · rw [← h']; simp
            · simp [show k - τ.length ≠ 0 by omega]
          · simp [List.getElem?_append_left hk]
          · rw [List.getElem?_append_right hk, List.getElem?_append_right hk]
            rcases Nat.eq_or_lt_of_le hk with h' | h'
            · rw [← h']; simp [centR, hi]
            · simp [show k - τ.length ≠ 0 by omega]
        have hlast : (τ ++ [((msg, ⟨i, c⟩) : cEntE (F := F) (L := L) (m := m) ℓ κ)])[ℓ]? =
            some (msg, ⟨i, c⟩) := by
          rw [List.getElem?_append_right (by omega)]
          simp [show ℓ - τ.length = 0 by omega]
        have hg : cgOf (τ ++ [((msg, ⟨i, c⟩) : cEntE (F := F) (L := L) (m := m) ℓ κ)]) = msg.2.2 := by
          simp [cgOf, hlast]
        have hξ : cξOf (τ ++ [((msg, ⟨i, c⟩) : cEntE (F := F) (L := L) (m := m) ℓ κ)]) =
            chQ (κ := κ) hi c := by
          simp [cξOf, hlast, centQ, hi]
        simp only [cVE, hparse, hg, hξ]
      have hprob : prob (fun c : ChE (F := F) (L := L) ℓ κ i =>
          ¬ cDE ℓ κ δ (w0, (zp, zs), v) (τ ++ [((msg, ⟨i, c⟩) : cEntE (F := F) (L := L) (m := m) ℓ κ)])) =
          prob (fun ξ : Fin κ → L => cFullAccepts ℓ w0 zp zs v τr msg.2.2 ξ) := by
        rw [← prob_equiv (chQ (F := F) (L := L) (κ := κ) hi)]
        congr 1; funext c; exact propext (hpar c)
      rw [hprob] at hε
      have hdoom : cDoomed ℓ w0 zp zs v δ τr ℓ := by
        right
        rwa [cNotDoomed_congr (fun k hk => by
          obtain ⟨a1, a2, a3⟩ := cparse_append_lt τ ((msg, ⟨i, c0⟩) : cEntE (F := F) (L := L) (m := m) ℓ κ) (k := k) (by omega)
          exact ⟨a1, a2, a3⟩)]
      have := crbr_final hL hℓ hδ τr hdoom msg.2.2 κ
      exact absurd hε (not_lt.2 this)
  · -- condition 3
    rintro x τ hτ hD
    have hlen := clength_of_isPartial hτ
    simp only [cDE, hlen, Nat.add_one_ne_zero, if_false, show ¬ (ℓ + 1 ≤ ℓ) by omega] at hD
    exact hD

/-- **Theorem 6.20**, in the form of Definition 3.7 (`RBRKnowledge`). -/
theorem crbr_knowledge' {R : ℕ} (hL : IsSmoothDomain L (m + ℓ + R)) (hℓ : 1 ≤ ℓ) (hδ0 : 0 < δ)
    (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2) :
    RBRKnowledge (cVE (F := F) (L := L) (m := m) ℓ κ) (cRE ℓ δ) (cεE (L := L) ℓ κ δ) :=
  ⟨_, _, crbr_knowledge κ hL hℓ hδ0 hδ⟩

omit [Fintype F] [DecidableEq F] [Fintype L] in
/-- Condition `eq:dist-unique` for `dist = Δ^fib₀` (§6.6, "Relation"): by Lemma 6.3 and the
injectivity of `Enc`. -/
theorem cuniqueWithin_fib {R : ℕ} (hL : IsSmoothDomain L (m + ℓ + R)) (hℓ : 1 ≤ ℓ)
    (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2) :
    UniqueWithin (cEnc L (n := m + ℓ) (F := F)) fibDist δ := by
  intro w f f' h1 h1'
  haveI := hL.finite
  have hd : 2 ^ (m + ℓ) ≤ Nat.card L := Nd_le_card hL (j := 0) (by omega)
  have hrate : rate L (2 ^ (m + ℓ)) = 1 / 2 ^ R := rate_lv hL (j := 0) (by omega)
  have hδ' : δ ≤ (1 - rate L (2 ^ (m + ℓ))) / 2 := by rw [hrate]; exact hδ
  have hneg : (-1 : Fˣ) ∈ L := hL.neg_one_mem (by omega)
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_smooth hL (by omega)
  exact cEnc_injective hd (fib_unique hneg h2 hδ' w (cEnc_mem_RS L f) (cEnc_mem_RS L f') h1 h1')

/-- **Remark 6.21:** by Lemma 3.12, Theorem 6.20 implies that `Π_eval` (as a generic IOP) is
`ε`-evaluation binding (Definition 3.11) with `ε = ∑_{j=1}^{ℓ} (M_j+1)/|F| + (1-δ)^κ`. -/
theorem crbr_binding {R : ℕ} (hL : IsSmoothDomain L (m + ℓ + R)) (hℓ : 1 ≤ ℓ) (hδ0 : 0 < δ)
    (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2) :
    EvalBinding (cVE (F := F) (L := L) (m := m) ℓ κ) (∑ i, cεE (L := L) ℓ κ δ i) := by
  have hR : (0 : ℚ) < 1 / 2 ^ R := by positivity
  refine rbr_knowledge_binding (cEnc L) fibDist δ _ _ (cεE (L := L) ℓ κ δ) ?_
    (crbr_knowledge' κ hL hℓ hδ0 hδ) (cuniqueWithin_fib hL hℓ hδ)
  intro i
  simp only [cεE]
  split_ifs
  · positivity
  · exact pow_nonneg (by linarith) κ

end Main

end SumFRI
