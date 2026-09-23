/-
KBFold/RBR.lean
§7.6 of the paper: round-by-round knowledge soundness of `Π_eval` (unique-decoding regime).
* Definition 7.16 (doomed set and extractor): `NotDoomed`, `Doomed`, `Ext`, with the auxiliary
  objects of §7.6 (`what` = `ŵ_j`, `Wset` = `𝒲_j(c)`, `dens`, `sigmaJ` = `σ_j(c)`);
* Lemma 7.17 (one round of the chain) `rbr_step`;
* Lemma 7.18 (honest round polynomial for a codeword) `sC`, `sC_zero_add_one`, `sC_eval`,
  and its instance at level `j` (`sCw_zero_add_one`, `sCw_eval`);
* Theorem 7.19 items 1–3: `rbr_round_one`, `rbr_round`, `rbr_final`;
* Proposition 7.21 (`ℓ = 0`): `rbr_l0`.

Modelling of partial transcripts.  A partial transcript is given by its data `τ : PTrans F L`:
the round polynomials `τ.s i` (the paper's `s_{i+1}`), the oracles `τ.w j` (`w_j`,
`1 ≤ j ≤ ℓ-1`) and the challenges `τ.r i` (`r_{i+1}`); the instance `(w₀; z, v)` is separate.
The predicate "`τ_j` is (not) doomed" (`NotDoomed … τ j`) only reads `s_i, r_i` for `i < j` and
`w_i` for `i < j`; the items of Theorem 7.19 quantify over *all* data `τ` (hence over all
earlier transcripts and all round-`j` messages), and the probability is over the challenge
`r_j`, which is substituted with `updR τ (j-1) c`.  Round polynomials are required to lie in
`F[X]_{<3}` (they are transmitted as three values).  The connection with the generic transcript
model of `KBFold/RoundByRound.lean` (Definition 3.7, `IsRBRKnowledgeWith`), i.e. Theorem 7.19's
"Consequently", is in `KBFold/RBRGeneric.lean`.
-/
import KBFold.Soundness

set_option autoImplicit false

open Polynomial Finset

namespace KBFold

variable {F : Type*} [Field F]

/-! ### Auxiliary facts -/

section Aux

variable {L : Subgroup Fˣ}

/-- The power map `ξ ↦ ξ^{2^j}` is `2^j`-to-one from `L` onto `L_j` (Lemma 2.15(2)), in the
form: preimages have `2^j` times as many points. -/
theorem ncard_preimage_ptAt {μ : ℕ} (hL : IsSmoothDomain L μ) :
    ∀ j ≤ μ, ∀ T : Set (lv L j), ((fun ξ : L => ptAt ξ j) ⁻¹' T).ncard = 2 ^ j * T.ncard
  | 0, _, T => by simp only [pow_zero, one_mul]; rfl
  | j + 1, hj, T => by
      haveI := hL.finite
      haveI := lv_finite (L := L) j
      have e : ((fun ξ : L => ptAt ξ (j + 1)) ⁻¹' T) =
          (fun ξ : L => ptAt ξ j) ⁻¹' (sqPt ⁻¹' T) := rfl
      rw [e, ncard_preimage_ptAt hL j (by omega),
        ncard_preimage_sqPt (lv_neg_one_mem hL (by omega)) (two_ne_zero_of_smooth hL (by omega)),
        pow_succ]
      ring

/-- Transport of `λ~(x)` along an equality of numbers of variables. -/
lemma mle_coordsOf_congr (P : F[X]) {a b : ℕ} (h : a = b) (x : Fin a → F) (y : Fin b → F)
    (hxy : ∀ i : Fin b, x (Fin.cast h.symm i) = y i) :
    mle (coordsOf a P) x = mle (coordsOf b P) y := by
  subst h
  congr 1
  funext i
  exact hxy i

/-- The coordinates `z_1, …, z_n` of the point `z = catPt ℓ zp zs` as a sequence
(`zfull i` is the paper's `z_{i+1}`). -/
def zfull {m : ℕ} (ℓ : ℕ) (zp : ℕ → F) (zs : Fin m → F) (i : ℕ) : F :=
  if i < ℓ then zp i else if h : i - ℓ < m then zs ⟨i - ℓ, h⟩ else 0

lemma zfull_lt {m ℓ : ℕ} (zp : ℕ → F) (zs : Fin m → F) {i : ℕ} (h : i < ℓ) :
    zfull ℓ zp zs i = zp i := by simp [zfull, h]

lemma zfull_ge {m ℓ : ℕ} (zp : ℕ → F) (zs : Fin m → F) (i : Fin m) :
    zfull ℓ zp zs (ℓ + i) = zs i := by
  have h1 : ¬ (ℓ + (i : ℕ) < ℓ) := by omega
  have h2 : ℓ + (i : ℕ) - ℓ < m := by omega
  simp only [zfull, h1, if_false, h2, dif_pos]
  congr 1; ext; simp

theorem catPt_eq_zfull : ∀ (ℓ : ℕ) {m : ℕ} (zp : ℕ → F) (zs : Fin m → F) (i : Fin (m + ℓ)),
    catPt ℓ zp zs i = zfull ℓ zp zs i
  | 0, m, zp, zs, i => by
      have h : (i : ℕ) - 0 < m := by simp
      simp only [catPt, zfull, Nat.not_lt_zero, if_false, h, dif_pos]
      congr 1
  | ℓ + 1, m, zp, zs, i => by
      refine Fin.cases ?_ (fun i' => ?_) i
      · simp [catPt, zfull]
      · simp only [catPt, Fin.cons_succ]
        rw [catPt_eq_zfull ℓ (shiftSeq zp) zs i']
        simp only [zfull, shiftSeq, Fin.val_succ]
        by_cases h : (i' : ℕ) < ℓ
        · simp [h, show (i' : ℕ) + 1 < ℓ + 1 by omega]
        · have h' : ¬ ((i' : ℕ) + 1 < ℓ + 1) := by omega
          have e : (i' : ℕ) + 1 - (ℓ + 1) = i' - ℓ := by omega
          simp only [h, h', if_false]
          by_cases h3 : (i' : ℕ) - ℓ < m
          · rw [dif_pos h3, dif_pos (by omega)]
            congr 1; ext; simp [e]
          · rw [dif_neg h3, dif_neg (by omega)]

/-- `prob[ξ₁,…,ξ_κ ∈ S] = (|S|/|L|)^κ` for independent uniform query points. -/
lemma prob_forall_mem {Λ : Type*} [Fintype Λ] [DecidableEq Λ] (κ : ℕ) (S : Finset Λ) :
    prob (fun ξ : Fin κ → Λ => ∀ t, ξ t ∈ S) = ((S.card : ℚ) / Fintype.card Λ) ^ κ := by
  classical
  rw [prob_def]
  have : (univ.filter fun ξ : Fin κ → Λ => ∀ t, ξ t ∈ S) = Fintype.piFinset (fun _ => S) := by
    ext ξ; simp
  rw [this, Fintype.card_piFinset, Fintype.card_fun, Fintype.card_fin]
  simp [div_pow]

end Aux

/-! ### Lemma 7.18 (honest round polynomial for a codeword), generic form -/

section RoundPolyC

/-- **Lemma 7.18:** the round polynomial
`s^c(X) = pre · ∑_b λ~(X, b) eq((X, b), (z_j, z'))` for a table `λ` with `k+1` variables (the
kernel coordinates of `P_c`), computed by equation (6.1) from `λ` and the equality table. -/
noncomputable def sC {k : ℕ} (pre : F) (lam : Table F (k + 1)) (zj : F) (z' : Fin k → F) : F[X] :=
  C pre * roundPoly lam (eqTable (Fin.cons zj z'))

theorem natDegree_sC {k : ℕ} (pre : F) (lam : Table F (k + 1)) (zj : F) (z' : Fin k → F) :
    (sC pre lam zj z').natDegree ≤ 2 :=
  (natDegree_C_mul_le _ _).trans (natDegree_roundPoly _ _)

/-- **Lemma 7.18:** `s^c(0) + s^c(1) = pre · λ~(z_j, z')`. -/
theorem sC_zero_add_one {k : ℕ} (pre : F) (lam : Table F (k + 1)) (zj : F) (z' : Fin k → F) :
    (sC pre lam zj z').eval 0 + (sC pre lam zj z').eval 1 = pre * mle lam (Fin.cons zj z') := by
  simp only [sC, eval_mul, eval_C]
  rw [← mul_add, roundPoly_zero_add_one, ipSum_eqTable]

/-- **Lemma 7.18:** `s^c(a) = pre · eq₁(a, z_j) · res_a(λ)~(z')`. -/
theorem sC_eval {k : ℕ} (pre : F) (lam : Table F (k + 1)) (zj : F) (z' : Fin k → F) (a : F) :
    (sC pre lam zj z').eval a = pre * eq1 a zj * mle (res a lam) z' := by
  simp only [sC, eval_mul, eval_C]
  rw [roundPoly_eval, res_eqTable, mul_assoc]
  congr 1
  simp only [ipSum, mle, eqTable, Pi.smul_apply, smul_eq_mul, mul_sum]
  refine sum_congr rfl (fun b _ => ?_)
  ring

/-- Proposition 5.8 + Theorem 5.3: the kernel coordinates of `fold_a(c)` are `res_a(λ[c])`. -/
theorem coordsOf_wfold {D : Subgroup Fˣ} [Finite D] (hD : (-1 : Fˣ) ∈ D) (h2 : (2 : F) ≠ 0)
    {k : ℕ} (hk : 2 * 2 ^ k ≤ Nat.card D) (hk' : 2 ^ k ≤ Nat.card (sqDom D)) {c : D → F}
    (hc : c ∈ RS D (2 * 2 ^ k)) (a : F) :
    coordsOf k (polyOf (wfold a c)) = res a (coordsOf (k + 1) (polyOf c)) := by
  rw [polyOf_wfold hD h2 a hk hk' hc]
  have hP : polyOf c ∈ degreeLT F (2 ^ (k + 1)) := by
    rw [pow_succ']; exact (polyOf_spec hk hc).1
  conv_lhs => rw [← ofCoords_coordsOf hP]
  rw [fold_dictionary, coordsOf_ofCoords]

end RoundPolyC

/-! ### Definition 7.16 (doomed set and extractor) -/

/-- The data of a partial transcript of `Π_eval` (§7.6): round polynomials `s i` (`s_{i+1}`),
oracles `w j` (`w_j` for `1 ≤ j ≤ ℓ-1`; `w 0` is ignored, the commitment `w₀` is part of the
instance), challenges `r i` (`r_{i+1}`). -/
structure PTrans (F : Type*) [Field F] (L : Subgroup Fˣ) where
  /-- round polynomials -/
  s : ℕ → F[X]
  /-- oracles -/
  w : (j : ℕ) → lv L j → F
  /-- challenges -/
  r : ℕ → F

/-- `τ` with the challenge `r_{j+1}` replaced by `c`. -/
def PTrans.updR {L : Subgroup Fˣ} (τ : PTrans F L) (j : ℕ) (c : F) : PTrans F L :=
  { τ with r := Function.update τ.r j c }

section Doomed

variable {L : Subgroup Fˣ} {m : ℕ} (ℓ : ℕ) (w0 : L → F) (zp : ℕ → F) (zs : Fin m → F) (v : F)
  (δ : ℚ)

/-- The words `w_0 = w₀` and `w_j = τ.w j`. -/
def Wd (τ : PTrans F L) : (j : ℕ) → lv L j → F
  | 0 => w0
  | j + 1 => τ.w (j + 1)

/-- `ŵ_{j+1} = fold_{r_{j+1}}(w_j) ∈ F^{L_{j+1}}` (§7.6, "Notation"). -/
noncomputable def what (τ : PTrans F L) (j : ℕ) : lv L (j + 1) → F :=
  wfold (τ.r j) (Wd w0 τ j)

/-- The witness sets (§7.6): `𝒲_0(c) = {ξ ∈ L : w₀(±ξ) = c(±ξ)}` and, for `j ≥ 1`,
`𝒲_j(c) = {ξ ∈ L : ξ^{2^i} ∉ ℬ_i for i ∈ [1, j-1], and ŵ_j(ξ^{2^j}) = c(ξ^{2^j})}`,
where `ℬ_i = {η ∈ L_i : ŵ_i(η) ≠ w_i(η)}`. -/
def Wset (τ : PTrans F L) : (j : ℕ) → (lv L j → F) → Set L
  | 0, c => {ξ | w0 ξ = c ξ ∧ w0 (negPt ξ) = c (negPt ξ)}
  | j + 1, c => {ξ | (∀ i < j, what w0 τ i (ptAt ξ (i + 1)) = Wd w0 τ (i + 1) (ptAt ξ (i + 1))) ∧
      what w0 τ j (ptAt ξ (j + 1)) = c (ptAt ξ (j + 1))}

/-- `dens_j(c) = |𝒲_j(c)| / M`. -/
noncomputable def dens (τ : PTrans F L) (j : ℕ) (c : lv L j → F) : ℚ :=
  ((Wset w0 τ j c).ncard : ℚ) / Nat.card L

/-- `σ_j(c) = (∏_{i ≤ j} eq₁(r_i, z_i)) · λ[c]~(z_{j+1}, …, z_n)`, with `λ[c]` the table of
kernel coordinates (with `n - j` variables) of `P_c`. -/
noncomputable def sigmaJ (τ : PTrans F L) (j : ℕ) (c : lv L j → F) : F :=
  (∏ i ∈ range j, eq1 (τ.r i) (zfull ℓ zp zs i)) *
    mle (coordsOf (m + ℓ - j) (polyOf c)) (fun i => zfull ℓ zp zs (j + i))

/-- The running claims `v_0 = v`, `v_{i+1} = s_{i+1}(r_{i+1})`. -/
noncomputable def vvT (τ : PTrans F L) : ℕ → F
  | 0 => v
  | i + 1 => (τ.s i).eval (τ.r i)

/-- The sumcheck checks of indices `1, …, j`. -/
def SCT (τ : PTrans F L) (j : ℕ) : Prop :=
  ∀ i < j, (τ.s i).eval 0 + (τ.s i).eval 1 = vvT v τ i

/-- **Definition 7.16:** for `j ∈ [1, ℓ]`, `τ_j` is *not doomed* iff the sumcheck checks of
indices `1, …, j` hold and some `c ∈ 𝒞_j` has `dens_j(c) ≥ 1-δ` and `v_j = σ_j(c)`. -/
def NotDoomed (τ : PTrans F L) (j : ℕ) : Prop :=
  SCT v τ j ∧ ∃ c ∈ RS (lv L j) (Nd m ℓ j), 1 - δ ≤ dens w0 τ j c ∧ vvT v τ j = sigmaJ ℓ zp zs τ j c

/-- **Definition 7.16:** the doomed set for partial transcripts: `τ_0` is doomed, and `τ_j`
(`1 ≤ j ≤ ℓ`) is doomed iff it is not "not doomed".  (A full transcript is doomed iff the
verifier rejects it; see `FullAccepts`.) -/
def Doomed (τ : PTrans F L) (j : ℕ) : Prop := j = 0 ∨ ¬ NotDoomed ℓ w0 zp zs v δ τ j

/-- The prover whose messages are those of `τ` (and final table `g`), used to run the verifier
of §6.2 on a full transcript. -/
def proverOf (τ : PTrans F L) (g : Table F m) : EvalProver F L m :=
  ⟨fun i _ => τ.s i, fun j _ => τ.w j, fun _ => g⟩

/-- The verifier accepts the full transcript `(τ, g, ξ)`. -/
def FullAccepts {κ : ℕ} (τ : PTrans F L) (g : Table F m) (ξ : Fin κ → L) : Prop :=
  (proverOf τ g).Accepts ℓ w0 zp zs v τ.r ξ

/-- The relation `R^δ_eval` with `dist = Δ^fib₀` (§7.6, "Relation"): `f` is a witness for
`(w₀; z, v)` iff `Δ^fib₀(w₀, Enc(f)) ≤ δ` and `f~(z) = v`. -/
def IsWitness (f : Table F (m + ℓ)) : Prop :=
  fibDist w0 (Enc L f) ≤ δ ∧ mle f (catPt ℓ zp zs) = v

/-- **Definition 7.16 (extractor):** the decoded table of `w₀` if `Δ^fib₀(w₀, 𝒞₀) ≤ δ`, and the
zero table otherwise. -/
noncomputable def Ext : Table F (m + ℓ) := by
  classical exact
    if FibDistLE w0 (RS L (2 ^ (m + ℓ)) : Set (L → F)) δ then decTable L (m + ℓ) δ w0 else 0

/-- The output of `Ext` is a witness iff `Δ^fib₀(w₀, 𝒞₀) ≤ δ` and `f*~(z) = v` (§7.6, after
Definition 7.16; for the "if" direction). -/
theorem Ext_witness_of {R : ℕ} (hL : IsSmoothDomain L (m + ℓ + R))
    (hF : FibDistLE w0 (RS L (2 ^ (m + ℓ)) : Set (L → F)) δ)
    (hv : mle (decTable L (m + ℓ) δ w0) (catPt ℓ zp zs) = v) :
    IsWitness ℓ w0 zp zs v δ (Ext ℓ w0 δ) := by
  classical
  haveI := hL.finite
  have hE : Ext ℓ w0 δ = decTable L (m + ℓ) δ w0 := by simp [Ext, hF]
  rw [IsWitness, hE, decTable_spec (show 2 ^ (m + ℓ) ≤ Nat.card L from
    Nd_le_card hL (j := 0) (by omega)) hF]
  exact ⟨(dec_spec hF).2, hv⟩

end Doomed

/-! ### Congruence: `τ_j` only depends on `r_{≤ j}` -/

section Congr

variable {L : Subgroup Fˣ} {m : ℕ} {ℓ : ℕ} {w0 : L → F} {zp : ℕ → F} {zs : Fin m → F} {v : F}
  {δ : ℚ}

lemma Wd_updR (τ : PTrans F L) (j : ℕ) (c : F) : Wd w0 (τ.updR j c) = Wd w0 τ := by
  funext i; cases i <;> rfl

lemma what_updR_lt (τ : PTrans F L) {j i : ℕ} (c : F) (hi : i < j) :
    what w0 (τ.updR j c) i = what w0 τ i := by
  simp only [what]
  rw [Wd_updR]
  simp only [PTrans.updR, Function.update_of_ne (show i ≠ j by omega)]

lemma what_updR_eq (τ : PTrans F L) (j : ℕ) (c : F) :
    what w0 (τ.updR j c) j = wfold c (Wd w0 τ j) := by
  simp only [what]
  rw [Wd_updR]
  simp only [PTrans.updR, Function.update_self]

lemma vvT_updR (τ : PTrans F L) (j : ℕ) (c : F) : ∀ i ≤ j, vvT v (τ.updR j c) i = vvT v τ i
  | 0, _ => rfl
  | i + 1, hi => by
      simp only [vvT, PTrans.updR, Function.update_of_ne (show i ≠ j by omega)]

lemma Wset_updR (τ : PTrans F L) (j : ℕ) (c : F) (c' : lv L j → F) :
    Wset w0 (τ.updR j c) j c' = Wset w0 τ j c' := by
  cases j with
  | zero => rfl
  | succ k =>
    ext ξ
    simp only [Wset, Set.mem_setOf_eq, Wd_updR]
    rw [what_updR_lt τ c (by omega : k < k + 1)]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨fun i hi => by rw [← what_updR_lt τ c (by omega : i < k + 1)]; exact h1 i hi, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨fun i hi => by rw [what_updR_lt τ c (by omega : i < k + 1)]; exact h1 i hi, h2⟩

lemma sigmaJ_updR (τ : PTrans F L) (j : ℕ) (c : F) (c' : lv L j → F) :
    sigmaJ ℓ zp zs (τ.updR j c) j c' = sigmaJ ℓ zp zs τ j c' := by
  simp only [sigmaJ]
  congr 1
  refine prod_congr rfl (fun i hi => ?_)
  simp only [PTrans.updR, Function.update_of_ne (show i ≠ j by simp at hi; omega)]

/-- `τ_j` does not depend on the challenge `r_{j+1}`. -/
theorem NotDoomed_updR (τ : PTrans F L) (j : ℕ) (c : F) :
    NotDoomed ℓ w0 zp zs v δ (τ.updR j c) j ↔ NotDoomed ℓ w0 zp zs v δ τ j := by
  simp only [NotDoomed, SCT, dens, Wset_updR, sigmaJ_updR, vvT_updR τ j c j le_rfl]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i hi => ?_, h2⟩
    have := h1 i hi
    rw [vvT_updR τ j c i hi.le] at this
    exact this
  · rintro ⟨h1, h2⟩
    refine ⟨fun i hi => ?_, h2⟩
    rw [vvT_updR τ j c i hi.le]
    exact h1 i hi

end Congr

/-! ### Lemma 7.17 (one round of the chain) -/

section Step

variable {L : Subgroup Fˣ} {m : ℕ} {ℓ : ℕ} {w0 : L → F} {δ : ℚ}

/-- **Lemma 7.17 (one round of the chain).** Let `j < ℓ` (the paper's round `j+1`), and let
`r_{j+1}` be good for `w_j`.  If `c' ∈ 𝒞_{j+1}` has `dens_{j+1}(c') ≥ 1-δ`, then
`Δ^fib_j(w_j, 𝒞_j) ≤ δ`, the codeword `c = dec_j(w_j)` satisfies `fold_{r_{j+1}}(c) = c'`, and
`𝒲_{j+1}(c') ⊆ 𝒲_j(c)`. -/
theorem rbr_step {R : ℕ} (hL : IsSmoothDomain L (m + ℓ + R)) (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2)
    (τ : PTrans F L) {j : ℕ} (hj : j < ℓ) (hgood : GoodAt ℓ δ m j (Wd w0 τ j) (τ.r j))
    (c' : lv L (j + 1) → F) (hc' : c' ∈ RS (lv L (j + 1)) (Nd m ℓ (j + 1)))
    (hdens : 1 - δ ≤ dens w0 τ (j + 1) c') :
    FibDistLE (Wd w0 τ j) (RS (lv L j) (2 * Nd m ℓ (j + 1)) : Set _) δ ∧
      wfold (τ.r j) (decAt ℓ δ m j (Wd w0 τ j)) = c' ∧
      Wset w0 τ (j + 1) c' ⊆ Wset w0 τ j (decAt ℓ δ m j (Wd w0 τ j)) := by
  obtain ⟨hDj, hμj, hdD, hrate⟩ := level_facts hL hj
  have hδj : δ ≤ (1 - rate (sqDom (lv L j)) (Nd m ℓ (j + 1))) / 2 := by rw [hrate]; exact hδ
  haveI := hL.finite
  haveI : Finite (sqDom (lv L j)) := lv_finite (L := L) (j + 1)
  haveI := lv_finite (L := L) (j + 1)
  set Y := agreeSet (what w0 τ j) c'
  have hsubY : Wset w0 τ (j + 1) c' ⊆ (fun ξ : L => ptAt ξ (j + 1)) ⁻¹' Y := by
    intro ξ hξ; exact hξ.2
  have hcardW : (Wset w0 τ (j + 1) c').ncard ≤ 2 ^ (j + 1) * Y.ncard := by
    rw [← ncard_preimage_ptAt hL (j + 1) (by omega) Y]
    exact Set.ncard_le_ncard hsubY (Set.toFinite _)
  have hML : Nat.card L = 2 ^ (j + 1) * Nat.card (lv L (j + 1)) := by
    rw [show Nat.card L = Nat.card (lv L 0) from rfl, card_lv hL (by omega),
      card_lv hL (by omega), ← pow_add]
    congr 1; omega
  have hLpos : (0 : ℚ) < Nat.card L := by
    haveI : Nonempty L := ⟨1⟩; exact_mod_cast Nat.card_pos
  have hY : (1 - δ) * Nat.card (sqDom (lv L j)) ≤ Y.ncard := by
    have h1 : (1 - δ) * Nat.card L ≤ (Wset w0 τ (j + 1) c').ncard := by
      rw [dens, le_div_iff₀ hLpos] at hdens; exact hdens
    have h2 : ((Wset w0 τ (j + 1) c').ncard : ℚ) ≤ 2 ^ (j + 1) * Y.ncard := by
      exact_mod_cast hcardW
    rw [hML] at h1
    push_cast at h1
    have h3 : (0 : ℚ) < 2 ^ (j + 1) := by positivity
    have : (1 - δ) * Nat.card (lv L (j + 1)) ≤ Y.ncard := by nlinarith
    exact this
  obtain ⟨hF, hfold, hagree⟩ := one_step hDj hμj hδj (Wd w0 τ j) (τ.r j) hgood c' hc' hY
  refine ⟨hF, hfold, fun ξ hξ => ?_⟩
  have hη : ptAt ξ (j + 1) ∈ Y := hξ.2
  have hfib1 : ptAt ξ j ∈ fibre (ptAt ξ (j + 1)) := rfl
  have hfib2 : negPt (ptAt ξ j) ∈ fibre (ptAt ξ (j + 1)) := negPt_mem_fibre hfib1
  cases j with
  | zero =>
    exact ⟨hagree _ hη _ hfib1, hagree _ hη _ hfib2⟩
  | succ k =>
    refine ⟨fun i hi => hξ.1 i (by omega), ?_⟩
    rw [hξ.1 k (by omega)]
    exact hagree _ hη _ hfib1

end Step

/-! ### Lemma 7.18 at level `j` and Theorem 7.19 -/

section Theorem

variable {L : Subgroup Fˣ} {m : ℕ} {ℓ : ℕ} {w0 : L → F} {zp : ℕ → F} {zs : Fin m → F} {v : F}
  {δ : ℚ}

variable (ℓ w0 zp zs δ) in
/-- **Lemma 7.18 at level `j`** (the paper's round `j+1`): the honest round polynomial
`s^c_{j+1}` for the codeword `c = dec_j(w_j)`, with prefix `∏_{i ≤ j} eq₁(r_i, z_i)`. -/
noncomputable def sCw (τ : PTrans F L) (j : ℕ) : F[X] :=
  sC (∏ i ∈ range j, eq1 (τ.r i) (zfull ℓ zp zs i))
    (coordsOf (m + ℓ - (j + 1) + 1) (polyOf (decAt ℓ δ m j (Wd w0 τ j))))
    (zfull ℓ zp zs j) (fun i => zfull ℓ zp zs (j + 1 + i))

lemma sCw_updR (τ : PTrans F L) (j : ℕ) (c : F) :
    sCw ℓ w0 zp zs δ (τ.updR j c) j = sCw ℓ w0 zp zs δ τ j := by
  simp only [sCw, Wd_updR]
  congr 1
  refine prod_congr rfl (fun i hi => ?_)
  simp only [PTrans.updR, Function.update_of_ne (show i ≠ j by simp at hi; omega)]

/-- **Lemma 7.18(2) at level `j`:** `s^c(0) + s^c(1) = σ_j(c)`. -/
theorem sCw_zero_add_one (τ : PTrans F L) {j : ℕ} (hj : j < ℓ) :
    (sCw ℓ w0 zp zs δ τ j).eval 0 + (sCw ℓ w0 zp zs δ τ j).eval 1 =
      sigmaJ ℓ zp zs τ j (decAt ℓ δ m j (Wd w0 τ j)) := by
  rw [sCw, sC_zero_add_one, sigmaJ]
  congr 1
  refine (mle_coordsOf_congr _ (show m + ℓ - j = m + ℓ - (j + 1) + 1 by omega) _ _ ?_).symm
  intro i
  refine Fin.cases ?_ (fun i' => ?_) i
  · simp
  · simp only [Fin.cons_succ, Fin.coe_cast, Fin.val_succ]
    congr 1; omega

/-- **Lemma 7.18(3) at level `j`:** `s^c(a) = σ_{j+1}(fold_a(c))`, where `σ_{j+1}` is computed
with `r_{j+1} = a`, for `c = dec_j(w_j) ∈ 𝒞_j`. -/
theorem sCw_eval {R : ℕ} (hL : IsSmoothDomain L (m + ℓ + R)) (τ : PTrans F L) {j : ℕ}
    (hj : j < ℓ) (hc : decAt ℓ δ m j (Wd w0 τ j) ∈ RS (lv L j) (2 * Nd m ℓ (j + 1))) (a : F) :
    (sCw ℓ w0 zp zs δ τ j).eval a =
      sigmaJ ℓ zp zs (τ.updR j a) (j + 1) (wfold a (decAt ℓ δ m j (Wd w0 τ j))) := by
  obtain ⟨hDj, hμj, hdD, -⟩ := level_facts hL hj
  haveI := hL.finite
  haveI := lv_finite (L := L) j
  have hneg := lv_neg_one_mem hL (j := j) (by omega)
  have h2F := two_ne_zero_of_smooth hL (by omega : 1 ≤ m + ℓ + R)
  have hk' : 2 ^ (m + ℓ - (j + 1)) ≤ Nat.card (sqDom (lv L j)) :=
    Nd_le_card hL (j := j + 1) (by omega)
  rw [sCw, sC_eval, sigmaJ, prod_range_succ]
  rw [coordsOf_wfold hneg h2F hdD hk' hc a]
  simp only [PTrans.updR, Function.update_self]
  congr 2
  refine prod_congr rfl (fun i hi => ?_)
  simp only [Function.update_of_ne (show i ≠ j by simp at hi; omega)]

variable (ℓ w0 zp zs δ) in
/-- The bad challenges of round `j+1` (proof of Theorem 7.19, items 1 and 2): `r_{j+1}` is not
good for `w_j`, or `Δ^fib_j(w_j, 𝒞_j) ≤ δ`, `s_{j+1} ≠ s^c_{j+1}` and
`s_{j+1}(r_{j+1}) = s^c_{j+1}(r_{j+1})`. -/
def BadR (τ : PTrans F L) (j : ℕ) (a : F) : Prop :=
  ¬ GoodAt ℓ δ m j (Wd w0 τ j) a ∨
    (FibDistLE (Wd w0 τ j) (RS (lv L j) (2 * Nd m ℓ (j + 1)) : Set _) δ ∧
      τ.s j ≠ sCw ℓ w0 zp zs δ τ j ∧ (τ.s j).eval a = (sCw ℓ w0 zp zs δ τ j).eval a)

/-- At most `M_{j+1} + 2` challenges are bad (Lemmas 7.9 and 2.1). -/
theorem card_BadR [Fintype F] [DecidableEq F] {R : ℕ} (hL : IsSmoothDomain L (m + ℓ + R))
    (hδ0 : 0 < δ) (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2) (τ : PTrans F L) {j : ℕ} (hj : j < ℓ)
    (hdeg : (τ.s j).natDegree ≤ 2) :
    ({a : F | BadR ℓ w0 zp zs δ τ j a}.ncard : ℚ) ≤ Nat.card (lv L (j + 1)) + 2 := by
  classical
  have hset : {a : F | BadR ℓ w0 zp zs δ τ j a} =
      {a : F | ¬ GoodAt ℓ δ m j (Wd w0 τ j) a} ∪
      {a : F | FibDistLE (Wd w0 τ j) (RS (lv L j) (2 * Nd m ℓ (j + 1)) : Set _) δ ∧
        τ.s j ≠ sCw ℓ w0 zp zs δ τ j ∧ (τ.s j).eval a = (sCw ℓ w0 zp zs δ τ j).eval a} := by
    ext a; simp only [BadR, Set.mem_setOf_eq, Set.mem_union]
  rw [hset]
  refine (Nat.cast_le.2 (Set.ncard_union_le _ _)).trans ?_
  push_cast
  apply add_le_add
  · exact_mod_cast card_badFold_le hL hδ0 hδ hj _
  · by_cases h : FibDistLE (Wd w0 τ j) (RS (lv L j) (2 * Nd m ℓ (j + 1)) : Set _) δ ∧
        τ.s j ≠ sCw ℓ w0 zp zs δ τ j
    · have e : {a : F | FibDistLE (Wd w0 τ j) (RS (lv L j) (2 * Nd m ℓ (j + 1)) : Set _) δ ∧
          τ.s j ≠ sCw ℓ w0 zp zs δ τ j ∧ (τ.s j).eval a = (sCw ℓ w0 zp zs δ τ j).eval a} =
          {a : F | (τ.s j).eval a = (sCw ℓ w0 zp zs δ τ j).eval a} := by
        ext a; simp [h.1, h.2]
      rw [e, ← card_filter_eq_ncard]
      exact_mod_cast card_agree_le_two _ _ h.2 hdeg (natDegree_sC _ _ _ _)
    · have e : {a : F | FibDistLE (Wd w0 τ j) (RS (lv L j) (2 * Nd m ℓ (j + 1)) : Set _) δ ∧
          τ.s j ≠ sCw ℓ w0 zp zs δ τ j ∧ (τ.s j).eval a = (sCw ℓ w0 zp zs δ τ j).eval a} = ∅ := by
        ext a
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        exact fun h' => h ⟨h'.1, h'.2.1⟩
      rw [e]; simp

/-- Core of the proof of Theorem 7.19, items 1 and 2: if `r_{j+1} = a` is not bad and `τ_{j+1}`
is not doomed, then `Δ^fib_j(w_j, 𝒞_j) ≤ δ`, `v_j = σ_j(c)` and `τ_j` satisfies the conditions
of Definition 7.16 with `c = dec_j(w_j)` (sumcheck checks `1..j`, `dens_j(c) ≥ 1-δ`). -/
theorem rbr_escape {R : ℕ} (hL : IsSmoothDomain L (m + ℓ + R)) (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2)
    (τ : PTrans F L) {j : ℕ} (hj : j < ℓ) (a : F) (hbad : ¬ BadR ℓ w0 zp zs δ τ j a)
    (hnd : NotDoomed ℓ w0 zp zs v δ (τ.updR j a) (j + 1)) :
    FibDistLE (Wd w0 τ j) (RS (lv L j) (2 * Nd m ℓ (j + 1)) : Set _) δ ∧
      SCT v τ j ∧ 1 - δ ≤ dens w0 τ j (decAt ℓ δ m j (Wd w0 τ j)) ∧
      vvT v τ j = sigmaJ ℓ zp zs τ j (decAt ℓ δ m j (Wd w0 τ j)) := by
  obtain ⟨hSC, c', hc', hdens, hv⟩ := hnd
  simp only [BadR, not_or, not_and, not_not] at hbad
  obtain ⟨hgood, hsum⟩ := hbad
  have hgood' : GoodAt ℓ δ m j (Wd w0 (τ.updR j a) j) ((τ.updR j a).r j) := by
    rw [Wd_updR]; simpa [PTrans.updR] using hgood
  obtain ⟨hF, hfold, hsub⟩ := rbr_step hL hδ (τ.updR j a) hj hgood' c' hc' hdens
  rw [Wd_updR] at hF hfold hsub
  simp only [PTrans.updR, Function.update_self] at hfold
  set cs := decAt ℓ δ m j (Wd w0 τ j)
  have hcs : cs ∈ RS (lv L j) (2 * Nd m ℓ (j + 1)) := (dec_spec hF).1
  -- `s_{j+1}(a) = s^c(a)`, hence `s_{j+1} = s^c`
  have hsa : (τ.s j).eval a = (sCw ℓ w0 zp zs δ τ j).eval a := by
    rw [sCw_eval hL τ hj hcs a, hfold, ← hv]
    simp [vvT, PTrans.updR]
  have hs : τ.s j = sCw ℓ w0 zp zs δ τ j := by
    by_contra hne; exact hsum hF hne hsa
  -- the sumcheck check of index `j+1`
  have hck := hSC j (by omega)
  rw [vvT_updR τ j a j le_rfl, show (τ.updR j a).s = τ.s from rfl, hs,
    sCw_zero_add_one τ hj] at hck
  refine ⟨hF, fun i hi => ?_, ?_, hck.symm⟩
  · have := hSC i (by omega)
    rwa [vvT_updR τ j a i hi.le] at this
  · have hsub' : Wset w0 (τ.updR j a) (j + 1) c' ⊆ Wset w0 τ j cs := by
      rw [Wset_updR] at hsub; exact hsub
    have hle : (Wset w0 (τ.updR j a) (j + 1) c').ncard ≤ (Wset w0 τ j cs).ncard := by
      haveI := hL.finite
      exact Set.ncard_le_ncard hsub' (Set.toFinite _)
    refine hdens.trans ?_
    rw [dens, dens]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hle) (Nat.cast_nonneg _)

/-- **Theorem 7.19, item 1 (round 1).** If the output of `Ext` is not a witness for
`(w₀; z, v)`, then for every round-1 message `s_1 ∈ F[X]_{<3}`, `τ_1` is not doomed with
probability at most `(M_1 + 2)/|F|` over `r_1`. -/
theorem rbr_round_one [Fintype F] [DecidableEq F] {R : ℕ} (hL : IsSmoothDomain L (m + ℓ + R))
    (hℓ : 1 ≤ ℓ) (hδ0 : 0 < δ) (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2)
    (hnw : ¬ IsWitness ℓ w0 zp zs v δ (Ext ℓ w0 δ)) (τ : PTrans F L)
    (hdeg : (τ.s 0).natDegree ≤ 2) :
    prob (fun a : F => NotDoomed ℓ w0 zp zs v δ (τ.updR 0 a) 1) ≤
      ((Nat.card (lv L 1) : ℚ) + 2) / Fintype.card F := by
  classical
  have hsub : ∀ a, NotDoomed ℓ w0 zp zs v δ (τ.updR 0 a) 1 → BadR ℓ w0 zp zs δ τ 0 a := by
    intro a hnd
    by_contra hbad
    obtain ⟨hF, -, -, hv⟩ := rbr_escape hL hδ τ (by omega) a hbad hnd
    have e0 : 2 * Nd m ℓ (0 + 1) = 2 ^ (m + ℓ) := by rw [Nd_succ (by omega)]; rfl
    have hF0 : FibDistLE w0 (RS L (2 ^ (m + ℓ)) : Set (L → F)) δ := by
      have := hF; rw [e0] at this; exact this
    apply hnw
    refine Ext_witness_of ℓ w0 zp zs v δ hL hF0 ?_
    -- `v = v_0 = σ_0(c) = f*~(z)`
    have hv' : v = sigmaJ ℓ zp zs τ 0 (decAt ℓ δ m 0 w0) := hv
    rw [hv', sigmaJ]
    simp only [range_zero, prod_empty, one_mul, decAt, decTable]
    rw [e0]
    refine mle_coordsOf_congr _ rfl _ _ (fun i => ?_)
    rw [catPt_eq_zfull]
    simp
  calc prob (fun a : F => NotDoomed ℓ w0 zp zs v δ (τ.updR 0 a) 1)
      ≤ prob (fun a : F => BadR ℓ w0 zp zs δ τ 0 a) := prob_mono hsub
    _ ≤ _ := by
        rw [prob_def, card_filter_eq_ncard]
        exact div_le_div_of_nonneg_right (card_BadR hL hδ0 hδ τ (by omega) hdeg)
          (Nat.cast_nonneg _)

/-- **Theorem 7.19, item 2 (round `j+1`, `1 ≤ j < ℓ`).** If `τ_j` is doomed, then for every
round-`(j+1)` message `(w_j, s_{j+1})` (with `s_{j+1} ∈ F[X]_{<3}`), `τ_{j+1}` is not doomed with
probability at most `(M_{j+1} + 2)/|F|` over `r_{j+1}`. -/
theorem rbr_round [Fintype F] [DecidableEq F] {R : ℕ} (hL : IsSmoothDomain L (m + ℓ + R))
    (hδ0 : 0 < δ) (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2) (τ : PTrans F L) {j : ℕ} (hj1 : 1 ≤ j)
    (hj : j < ℓ) (hdoom : Doomed ℓ w0 zp zs v δ τ j) (hdeg : (τ.s j).natDegree ≤ 2) :
    prob (fun a : F => NotDoomed ℓ w0 zp zs v δ (τ.updR j a) (j + 1)) ≤
      ((Nat.card (lv L (j + 1)) : ℚ) + 2) / Fintype.card F := by
  classical
  have hnd : ¬ NotDoomed ℓ w0 zp zs v δ τ j := by
    rcases hdoom with h | h
    · omega
    · exact h
  have hsub : ∀ a, NotDoomed ℓ w0 zp zs v δ (τ.updR j a) (j + 1) → BadR ℓ w0 zp zs δ τ j a := by
    intro a hnd'
    by_contra hbad
    obtain ⟨hF, hSC, hdens, hv⟩ := rbr_escape hL hδ τ hj a hbad hnd'
    apply hnd
    have hmem := (dec_spec hF).1
    change decAt ℓ δ m j (Wd w0 τ j) ∈ (RS (lv L j) (2 * Nd m ℓ (j + 1)) : Set _) at hmem
    generalize decAt ℓ δ m j (Wd w0 τ j) = cs at hmem hdens hv
    rw [Nd_succ (by omega)] at hmem
    exact ⟨hSC, cs, hmem, hdens, hv⟩
  calc prob (fun a : F => NotDoomed ℓ w0 zp zs v δ (τ.updR j a) (j + 1))
      ≤ prob (fun a : F => BadR ℓ w0 zp zs δ τ j a) := prob_mono hsub
    _ ≤ _ := by
        rw [prob_def, card_filter_eq_ncard]
        exact div_le_div_of_nonneg_right (card_BadR hL hδ0 hδ τ hj hdeg) (Nat.cast_nonneg _)

/-- **Theorem 7.19, item 3 (round `ℓ+1`).** If `τ_ℓ` is doomed, then for every final message
`g`, the verifier accepts with probability at most `(1-δ)^κ` over the query points. -/
theorem rbr_final [Fintype L] {R : ℕ} (hL : IsSmoothDomain L (m + ℓ + R)) (hℓ : 1 ≤ ℓ)
    (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2) (τ : PTrans F L) (hdoom : Doomed ℓ w0 zp zs v δ τ ℓ)
    (g : Table F m) (κ : ℕ) :
    prob (fun ξ : Fin κ → L => FullAccepts ℓ w0 zp zs v τ g ξ) ≤ (1 - δ) ^ κ := by
  classical
  have hR : (0 : ℚ) < 1 / 2 ^ R := by positivity
  have hδ1 : (0 : ℚ) ≤ 1 - δ := by linarith
  have hnd : ¬ NotDoomed ℓ w0 zp zs v δ τ ℓ := by
    rcases hdoom with h | h
    · omega
    · exact h
  haveI := hL.finite
  haveI : Nonempty L := ⟨1⟩
  haveI := lv_finite (L := L) ℓ
  set Pτ := proverOf τ g
  set wl := ev (lv L ℓ) (ofCoords g)
  -- the words of the verifier are those of `τ`
  have hW : ∀ i < ℓ, Pτ.W ℓ w0 τ.r i = Wd w0 τ i := by
    intro i hi
    cases i with
    | zero => rfl
    | succ k => simp only [EvalProver.W, if_neg (show k + 1 ≠ ℓ by omega)]; rfl
  have hWl : Pτ.W ℓ w0 τ.r ℓ = wl := W_last Pτ w0 hℓ τ.r
  have hvv : ∀ i, Pτ.vv v τ.r i = vvT v τ i := by intro i; cases i <;> rfl
  by_cases hSC : SCT v τ ℓ ∧ Pτ.ClosureOK ℓ zp zs v τ.r
  · obtain ⟨hSC, hCl⟩ := hSC
    -- `λ[w_ℓ] = g`, so the closure check reads `v_ℓ = σ_ℓ(w_ℓ)`
    have hd : 2 ^ m ≤ Nat.card (lv L ℓ) := by
      rw [← Nd_last (ℓ := ℓ)]; exact Nd_le_card hL (by omega)
    have hpoly : polyOf wl = ofCoords g :=
      polyOf_ev (degreeLT_mono' hd (ofCoords_mem_degreeLT g))
    have hσ : vvT v τ ℓ = sigmaJ ℓ zp zs τ ℓ wl := by
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
    have hdens : dens w0 τ ℓ wl < 1 - δ := by
      by_contra hge
      push_neg at hge
      exact hnd ⟨hSC, wl, hwl, hge, hσ⟩
    -- a query point passes all its checks iff it lies in `𝒲_ℓ(w_ℓ)`
    have hq : ∀ ξ : L, Pτ.QueryOK ℓ w0 τ.r ξ → ξ ∈ Wset w0 τ ℓ wl := by
      intro ξ hξ
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
    calc prob (fun ξ : Fin κ → L => FullAccepts ℓ w0 zp zs v τ g ξ)
        ≤ prob (fun ξ : Fin κ → L => ∀ t, ξ t ∈ (Set.toFinite (Wset w0 τ ℓ wl)).toFinset) := by
          apply prob_mono
          intro ξ hacc t
          rw [Set.Finite.mem_toFinset]
          exact hq _ (hacc.2.2 t)
      _ = (((Set.toFinite (Wset w0 τ ℓ wl)).toFinset.card : ℚ) / Fintype.card L) ^ κ :=
          prob_forall_mem κ _
      _ ≤ (1 - δ) ^ κ := by
          apply pow_le_pow_left₀ (by positivity)
          rw [← Set.ncard_eq_toFinset_card, ← Nat.card_eq_fintype_card]
          exact hdens.le
  · -- a sumcheck or the closure check fails: the verifier always rejects
    have : ∀ ξ : Fin κ → L, ¬ FullAccepts ℓ w0 zp zs v τ g ξ := by
      intro ξ hacc
      apply hSC
      refine ⟨fun i hi => ?_, hacc.2.1⟩
      have := hacc.1 i hi
      rwa [hvv] at this
    calc prob (fun ξ : Fin κ → L => FullAccepts ℓ w0 zp zs v τ g ξ)
        = prob (fun _ : Fin κ → L => False) := by
          congr 1; funext ξ; simp only [this ξ]
      _ = 0 := prob_false
      _ ≤ (1 - δ) ^ κ := pow_nonneg hδ1 κ

end Theorem

/-! ### Proposition 7.21 (round-by-round knowledge soundness for `ℓ = 0`) -/

section L0

variable {L : Subgroup Fˣ} {m : ℕ}

/-- The extractor of Proposition 7.21: the table `f^H` with `Δ(w₀, Enc(f^H)) ≤ δ` if there is
one (unique by Lemma 2.19(3)), and the zero table otherwise. -/
noncomputable def ExtH (w0 : L → F) (δ : ℚ) : Table F m := by
  classical exact if h : ∃ f : Table F m, relDist w0 (Enc L f) ≤ δ then h.choose else 0

/-- **Proposition 7.21 (round-by-round knowledge soundness for `ℓ = 0`).**  With
`dist = Δ`, the only round is the final one (`τ_0` is doomed, and a full transcript is doomed
iff rejected).  Condition 2 of Definition 3.7 for that round: for every final message `g`, if
the verifier accepts with probability greater than `(1-δ)^κ` over the query points, then the
output `f^H` of the extractor is a witness: `Δ(w₀, Enc(f^H)) ≤ δ` and `f^H~(z) = v`. -/
theorem rbr_l0 [Fintype L] {R : ℕ} (hL : IsSmoothDomain L (m + R)) {δ : ℚ}
    (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2) (w0 : L → F) (zp : ℕ → F) (zs : Fin m → F) (v : F)
    (τ : PTrans F L) (g : Table F m) (κ : ℕ)
    (hacc : (1 - δ) ^ κ < prob (fun ξ : Fin κ → L => FullAccepts 0 w0 zp zs v τ g ξ)) :
    relDist w0 (Enc L (ExtH (m := m) w0 δ)) ≤ δ ∧ mle (ExtH (m := m) w0 δ) zs = v := by
  classical
  haveI := hL.finite
  haveI : Nonempty L := ⟨1⟩
  have hR : (0 : ℚ) < 1 / 2 ^ R := by positivity
  have hδ1 : (0 : ℚ) ≤ 1 - δ := by linarith
  let S : Finset L := univ.filter (fun ξ => w0 ξ = (ofCoords g).eval (((ξ : L) : Fˣ) : F))
  have hev : ∀ ξ : Fin κ → L, FullAccepts 0 w0 zp zs v τ g ξ ↔
      v = mle g zs ∧ ∀ t, ξ t ∈ S := by
    intro ξ
    rw [FullAccepts, accepts_zero]
    simp [S, proverOf]
  by_cases hv : v = mle g zs
  · have hp : prob (fun ξ : Fin κ → L => FullAccepts 0 w0 zp zs v τ g ξ) =
        ((S.card : ℚ) / Fintype.card L) ^ κ := by
      rw [← prob_forall_mem κ S]
      congr 1; funext ξ; rw [hev ξ]; simp [hv]
    rw [hp] at hacc
    have hM : (0 : ℚ) < Fintype.card L := by exact_mod_cast Fintype.card_pos
    have hSM : 1 - δ < (S.card : ℚ) / Fintype.card L := by
      by_contra hle
      push_neg at hle
      have := pow_le_pow_left₀ (by positivity) hle κ
      linarith
    have hagree : agreeSet w0 (Enc L g) = (S : Set L) := by
      ext ξ; simp [agreeSet, S, Enc, ev]
    have hdist : relDist w0 (Enc L g) < δ := by
      have h := agree_add_hdist w0 (Enc L g)
      rw [hagree, Set.ncard_coe_finset] at h
      have h' : (S.card : ℚ) + hdist w0 (Enc L g) = Nat.card L := by exact_mod_cast h
      rw [Nat.card_eq_fintype_card] at h'
      unfold relDist
      rw [Nat.card_eq_fintype_card, div_lt_iff₀ hM]
      rw [lt_div_iff₀ hM] at hSM
      linarith
    have hex : ∃ f : Table F m, relDist w0 (Enc L f) ≤ δ := ⟨g, hdist.le⟩
    have hE : ExtH (m := m) w0 δ = hex.choose := by simp [ExtH, hex]
    have hspec := hex.choose_spec
    have hrate : rate L (2 ^ m) = 1 / 2 ^ R := rate_lv (ℓ := 0) hL (j := 0) (by omega)
    have hδ' : δ ≤ (1 - rate L (2 ^ m)) / 2 := by rw [hrate]; exact hδ
    have huniq := RS_unique_decoding' δ hδ' w0 (Enc_mem_RS L hex.choose) (Enc_mem_RS L g)
      hspec hdist.le
    have hfg : hex.choose = g := Enc_injective
      (show 2 ^ m ≤ Nat.card L from Nd_le_card (ℓ := 0) hL (j := 0) (by omega)) huniq
    rw [hE, hfg]
    exact ⟨hdist.le, hv.symm⟩
  · have : prob (fun ξ : Fin κ → L => FullAccepts 0 w0 zp zs v τ g ξ) = 0 := by
      rw [← prob_false (Ω := Fin κ → L)]
      congr 1; funext ξ; rw [hev ξ]; simp [hv]
    rw [this] at hacc
    have := pow_nonneg hδ1 κ
    linarith

end L0

end KBFold
