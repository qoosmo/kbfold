/-
KBFold/Protocol.lean
§6.1–6.3 of the paper: the domains `L_j`, the iterated folds, the protocol `Π_eval` for a
deterministic prover, and Lemma 6.4 (honest prover).

Modelling choices (see also the headers of `KBFold/Soundness.lean` and `KBFold/RBR.lean`).
* **Fields.**  As in `KBFold/Domain.lean`, a single field `F` with `L : Subgroup Fˣ`.
* **Levels.**  `lv L j` is the paper's `L_j = L^{2^j}`, defined by `lv L (j+1) = (lv L j)²`
  (`sqDom`), so that `fold_r` maps words on `lv L j` to words on `lv L (j+1)` *definitionally*.
  `lv_eq_iterDom` identifies it with `iterDom j L` of `KBFold/Domain.lean`.
  A query point `ξ₀ ∈ L` gives `ξ_j = ξ₀^{2^j}` as `ptAt ξ₀ j : lv L j`.
* **Number of variables.**  The number of variables is written `n = m + ℓ`, where `ℓ` is the
  number of folding rounds and `m = n - ℓ` the number of variables of the final table
  (so the paper's `1 ≤ ℓ ≤ n` is `1 ≤ ℓ`, and `0 ≤ ℓ ≤ n` is no condition).  The evaluation point
  `z ∈ F^n` is given as its first `ℓ` coordinates `zp : ℕ → F` (`zp i` is the paper's `z_{i+1}`)
  and its last `m` coordinates `zs : Fin m → F`; the point itself is `catPt ℓ zp zs`.
* **Indices are 0-based:** challenge `r i` is the paper's `r_{i+1}`, the round polynomial `s i` is
  the paper's `s_{i+1}`, and the query check `j` (for `j < ℓ`) is the paper's check at level
  `j+1`.  Challenges are a sequence `r : ℕ → F` (only `r 0, …, r (ℓ-1)` matter); the probability
  space `F^ℓ × L^κ` is `(Fin ℓ → F) × (Fin κ → L)`, with `extR` extending `Fin ℓ → F` to `ℕ → F`.
* **Deterministic prover.**  Following the paragraph "Fix a deterministic prover" of §7.3, a
  prover is given by its messages as functions of the challenges (`EvalProver`): the round
  polynomials `s i r ∈ F[X]` (transmitted as three values; any triple determines a unique
  polynomial of degree `≤ 2`, so we model the message as that polynomial, `DegOK`), the oracles
  `orc j r` for `1 ≤ j ≤ ℓ-1`, and the final table `g r`.  Causality (`Causal`: `s i` and `orc i`
  depend only on `r_{<i}`) is a hypothesis wherever it is used.
* **Verifier.**  `Accepts` is the conjunction of the sumcheck, closure and query checks of §6.2,
  with the oracle `w_ℓ = ev_{L_ℓ}(G)` computed by the verifier from `g`.
-/
import KBFold.Fibre
import KBFold.Probability

set_option autoImplicit false

open Polynomial Finset

namespace KBFold

variable {F : Type*} [Field F]

/-! ### The domains `L_j` and the points `ξ₀^{2^j}` -/

/-- The smooth domains `L_j = L^{2^j}` (§6.1): `lv L 0 = L`, `lv L (j+1) = (lv L j)²`. -/
def lv (L : Subgroup Fˣ) : ℕ → Subgroup Fˣ
  | 0 => L
  | j + 1 => sqDom (lv L j)

@[simp] lemma lv_zero (L : Subgroup Fˣ) : lv L 0 = L := rfl
lemma lv_succ (L : Subgroup Fˣ) (j : ℕ) : lv L (j + 1) = sqDom (lv L j) := rfl

/-- `lv L j = iterDom j L = L^{2^j}` (Lemma 2.15(3)). -/
theorem lv_eq_iterDom (L : Subgroup Fˣ) : ∀ j, lv L j = iterDom j L
  | 0 => rfl
  | j + 1 => by rw [lv_succ, lv_eq_iterDom L j, sqDom_iterDom]

/-- Lemma 2.15(2): `L_j` is a smooth domain of order `2^{μ-j}` (for `j ≤ μ`). -/
theorem lv_smooth {L : Subgroup Fˣ} {μ : ℕ} (hL : IsSmoothDomain L μ) {j : ℕ} (hj : j ≤ μ) :
    IsSmoothDomain (lv L j) (μ - j) := by
  rw [lv_eq_iterDom]; exact hL.iterDom_smooth hj

lemma lv_finite {L : Subgroup Fˣ} [Finite L] : ∀ j, Finite (lv L j)
  | 0 => ‹_›
  | j + 1 => by haveI := lv_finite (L := L) j; exact sqDom_finite

/-- `-1 ∈ L_j` for `j < μ` (Lemma 2.15(4)). -/
lemma lv_neg_one_mem {L : Subgroup Fˣ} {μ : ℕ} (hL : IsSmoothDomain L μ) {j : ℕ} (hj : j < μ) :
    (-1 : Fˣ) ∈ lv L j :=
  (lv_smooth hL hj.le).neg_one_mem (by omega)

/-- The point `ξ_j = ξ₀^{2^j}` of `L_j` for a query point `ξ₀ ∈ L` (§6.2, query checks). -/
def ptAt {L : Subgroup Fˣ} (ξ : L) : (j : ℕ) → lv L j
  | 0 => ξ
  | j + 1 => sqPt (ptAt ξ j)

lemma val_ptAt {L : Subgroup Fˣ} (ξ : L) : ∀ j, ((ptAt ξ j : Fˣ) : F) = ((ξ : Fˣ) : F) ^ (2 ^ j)
  | 0 => by simp [ptAt]
  | j + 1 => by
      rw [ptAt, val_sqPt, val_ptAt ξ j, ← pow_mul, pow_succ]

/-- Every point of `L_j` is some `ξ₀^{2^j}` (Lemma 2.15(2)). -/
lemma ptAt_surjective {L : Subgroup Fˣ} : ∀ j, Function.Surjective (fun ξ : L => ptAt ξ j)
  | 0 => fun η => ⟨η, rfl⟩
  | j + 1 => fun η => by
      obtain ⟨ξ, hξ⟩ := ptAt_surjective (L := L) j (sqrtPt η)
      exact ⟨ξ, by simp only [ptAt] at hξ ⊢; rw [hξ, sqPt_sqrtPt]⟩

/-- `ξ₀^{2^i}` is determined by `ξ₀^{2^j}` for `i ≥ j`. -/
lemma ptAt_congr {L : Subgroup Fˣ} {ξ ξ' : L} {j : ℕ} (h : ptAt ξ j = ptAt ξ' j) :
    ∀ i, j ≤ i → ptAt ξ i = ptAt ξ' i := by
  intro i hi
  induction i, hi using Nat.le_induction with
  | base => exact h
  | succ i _ ih => simp only [ptAt, ih]

/-! ### Iterated folds (Corollaries 5.4 and 5.9 on the levels `L_j`) -/

/-- The successive folds `fold_{r_j}(⋯ fold_{r_1}(w))` of a word `w` on `L` (a word on `L_j`). -/
noncomputable def foldUp {L : Subgroup Fˣ} (r : ℕ → F) (w : L → F) : (j : ℕ) → (lv L j → F)
  | 0 => w
  | j + 1 => wfold (r j) (foldUp r w j)

/-- The successive polynomial folds `pfold_{r_j}(⋯ pfold_{r_1}(U))`. -/
noncomputable def pfoldUp (r : ℕ → F) (U : F[X]) : ℕ → F[X]
  | 0 => U
  | j + 1 => pfold (r j) (pfoldUp r U j)

/-- `pfoldUp` agrees with `pfoldSeq` of `KBFold/WordFold.lean` (which folds from the front). -/
theorem pfoldSeq_succ' : ∀ (j : ℕ) (r : ℕ → F) (U : F[X]),
    pfoldSeq (j + 1) r U = pfold (r j) (pfoldSeq j r U)
  | 0, _, _ => rfl
  | j + 1, r, U => by
      rw [pfoldSeq, pfoldSeq_succ' j (shiftSeq r) (pfold (r 0) U)]
      rfl

theorem pfoldUp_eq_pfoldSeq (r : ℕ → F) (U : F[X]) : ∀ j, pfoldUp r U j = pfoldSeq j r U
  | 0 => rfl
  | j + 1 => by rw [pfoldUp, pfoldUp_eq_pfoldSeq r U j, pfoldSeq_succ']

/-- Proposition 5.8, iterated on the levels: `fold(⋯ fold(ev_L(U))) = ev_{L_j}(pfold(⋯ U))`. -/
theorem foldUp_ev {L : Subgroup Fˣ} (h2 : (2 : F) ≠ 0) (r : ℕ → F) (U : F[X]) :
    ∀ j, (∀ i < j, (-1 : Fˣ) ∈ lv L i) → foldUp r (ev L U) j = ev (lv L j) (pfoldUp r U j)
  | 0, _ => rfl
  | j + 1, h => by
      rw [foldUp, foldUp_ev h2 r U j (fun i hi => h i (by omega)), pfoldUp,
        wfold_ev (h j (by omega)) h2]
      rfl

/-- **Corollary 5.9 on the levels `L_j`:** for a table `λ` with `n = m + j` variables and
`j ≤ μ`, the `j`-th fold of `Enc(λ) = ev_L(U_λ)` is `ev_{L_j}(∑_b res_{r≤j}(λ)(b) K_b)`. -/
theorem foldUp_Enc {L : Subgroup Fˣ} {μ : ℕ} (hL : IsSmoothDomain L μ) {m j : ℕ} (hj : j ≤ μ)
    (r : ℕ → F) (lam : Table F (m + j)) :
    foldUp r (Enc L lam) j = ev (lv L j) (ofCoords (resSeq j r lam)) := by
  rcases Nat.eq_zero_or_pos j with rfl | hpos
  · rfl
  rw [Enc, foldUp_ev (two_ne_zero_of_smooth hL (by omega)) r _ j
    (fun i hi => lv_neg_one_mem hL (by omega)), pfoldUp_eq_pfoldSeq, pfoldSeq_ofCoords]

/-- `foldUp r w j` depends only on `r_{<j}`. -/
lemma foldUp_congr {L : Subgroup Fˣ} (w : L → F) {r r' : ℕ → F} :
    ∀ j, (∀ i < j, r i = r' i) → foldUp r w j = foldUp r' w j
  | 0, _ => rfl
  | j + 1, h => by
      rw [foldUp, foldUp, foldUp_congr w j (fun i hi => h i (by omega)), h j (by omega)]

/-! ### Lemma 6.4 (honest prover) -/

section Honest

/-- The equality table `χ = (b ↦ eq(b, z))` (§6.2, honest prover). -/
def eqTable {n : ℕ} (z : Fin n → F) : Table F n := fun b => eqv (pt b) z

/-- The inner product `∑_b f(b) χ(b)` of two tables. -/
def ipSum {n : ℕ} (f χ : Table F n) : F := ∑ b, f b * χ b

/-- The honest round polynomial (equation (6.1)) computed from the current tables `f, χ`:
`∑_{b'} ((1-X) f(2b') + X f(2b'+1)) ((1-X) χ(2b') + X χ(2b'+1))`. -/
noncomputable def roundPoly {k : ℕ} (f χ : Table F (k + 1)) : F[X] :=
  ∑ b : Fin k → Bool,
    (C (f (Fin.cons false b)) * (1 - X) + C (f (Fin.cons true b)) * X) *
      (C (χ (Fin.cons false b)) * (1 - X) + C (χ (Fin.cons true b)) * X)

/-- The honest round polynomials: `honS k r f χ j` is the round polynomial `s_{j+1}` of the
honest prover started on the tables `f, χ` with `k` variables beyond `m`, i.e. `roundPoly`
applied to the restricted tables `f_j = res_{r≤j}(f)`, `χ_j = res_{r≤j}(χ)`
(`honS (k+1) r f χ (j+1) = honS k (r ∘ succ) (res_{r₁} f) (res_{r₁} χ) j`). -/
noncomputable def honS {m : ℕ} : (k : ℕ) → (ℕ → F) → Table F (m + k) → Table F (m + k) → ℕ → F[X]
  | 0, _, _, _, _ => 0
  | _ + 1, _, f, χ, 0 => roundPoly f χ
  | k + 1, r, f, χ, j + 1 => honS k (shiftSeq r) (res (r 0) f) (res (r 0) χ) j

/-- The honest running values `σ_j = ∑_b f_j(b) χ_j(b)` (Lemma 6.4(3,4)). -/
noncomputable def honSig {m : ℕ} : (k : ℕ) → (ℕ → F) → Table F (m + k) → Table F (m + k) → ℕ → F
  | _, _, f, χ, 0 => ipSum f χ
  | 0, _, f, χ, _ + 1 => ipSum f χ
  | k + 1, r, f, χ, j + 1 => honSig k (shiftSeq r) (res (r 0) f) (res (r 0) χ) j

lemma lin_eval (a b x : F) : (C a * (1 - X) + C b * X).eval x = (1 - x) * a + x * b := by
  simp; ring

/-- `s(x) = ∑_{b'} res_x(f)(b') res_x(χ)(b')` for the honest round polynomial. -/
theorem roundPoly_eval {k : ℕ} (f χ : Table F (k + 1)) (x : F) :
    (roundPoly f χ).eval x = ipSum (res x f) (res x χ) := by
  unfold roundPoly ipSum res
  rw [eval_finset_sum]
  refine sum_congr rfl (fun b _ => ?_)
  rw [eval_mul, lin_eval, lin_eval]

/-- `s(0) + s(1) = ∑_b f(b) χ(b)` for the honest round polynomial. -/
theorem roundPoly_zero_add_one {k : ℕ} (f χ : Table F (k + 1)) :
    (roundPoly f χ).eval 0 + (roundPoly f χ).eval 1 = ipSum f χ := by
  rw [roundPoly_eval, roundPoly_eval, ipSum, ipSum, ipSum, sum_cons_bool, ← sum_add_distrib]
  refine sum_congr rfl (fun b _ => ?_)
  simp [res]

/-- The honest round polynomial has degree `≤ 2`. -/
theorem natDegree_roundPoly {k : ℕ} (f χ : Table F (k + 1)) : (roundPoly f χ).natDegree ≤ 2 := by
  unfold roundPoly
  apply natDegree_sum_le_of_forall_le
  intro b _
  have h1 : ∀ a c : F, (C a * (1 - X) + C c * X).natDegree ≤ 1 := by
    intro a c
    have : C a * (1 - X) + C c * X = C (c - a) * X + C a := by
      simp only [C_sub]; ring
    rw [this]
    exact natDegree_linear_le
  have ha := h1 (f (Fin.cons false b)) (f (Fin.cons true b))
  have hb := h1 (χ (Fin.cons false b)) (χ (Fin.cons true b))
  exact natDegree_mul_le.trans (by omega)

variable {m : ℕ}

/-- **Lemma 6.4(2)**, degree: `s_j ∈ F[X]_{<3}`. -/
theorem natDegree_honS : ∀ (k : ℕ) (r : ℕ → F) (f χ : Table F (m + k)) (j : ℕ),
    (honS k r f χ j).natDegree ≤ 2
  | 0, _, _, _, _ => by simp [honS]
  | _ + 1, _, f, χ, 0 => natDegree_roundPoly f χ
  | k + 1, r, f, χ, j + 1 => natDegree_honS k _ _ _ j

/-- The honest round polynomial `s_{j+1}` depends only on `r_{≤j}` (0-based: `r 0, …, r (j-1)`). -/
theorem honS_congr : ∀ (k : ℕ) (r r' : ℕ → F) (f χ : Table F (m + k)) (j : ℕ),
    (∀ i < j, r i = r' i) → honS k r f χ j = honS k r' f χ j
  | 0, _, _, _, _, _, _ => rfl
  | _ + 1, _, _, _, _, 0, _ => rfl
  | k + 1, r, r', f, χ, j + 1, h => by
      simp only [honS]
      rw [h 0 (by omega)]
      exact honS_congr k _ _ _ _ j (fun i hi => h (i + 1) (by omega))

/-- **Lemma 6.4(3)**, first identity: `s_{j+1}(r_{j+1}) = ∑_b f_{j+1}(b) χ_{j+1}(b)`. -/
theorem honS_eval : ∀ (k : ℕ) (r : ℕ → F) (f χ : Table F (m + k)) (j : ℕ), j < k →
    (honS k r f χ j).eval (r j) = honSig k r f χ (j + 1)
  | 0, _, _, _, _, h => absurd h (by omega)
  | k + 1, r, f, χ, 0, _ => by
      simp only [honS, honSig]
      rw [roundPoly_eval]
  | k + 1, r, f, χ, j + 1, h => by
      simp only [honS, honSig]
      exact honS_eval k (shiftSeq r) (res (r 0) f) (res (r 0) χ) j (by omega)

/-- **Lemma 6.4(3)**, second identity: `s_{j+1}(0) + s_{j+1}(1) = ∑_b f_j(b) χ_j(b)`. -/
theorem honS_zero_add_one : ∀ (k : ℕ) (r : ℕ → F) (f χ : Table F (m + k)) (j : ℕ), j < k →
    (honS k r f χ j).eval 0 + (honS k r f χ j).eval 1 = honSig k r f χ j
  | 0, _, _, _, _, h => absurd h (by omega)
  | k + 1, r, f, χ, 0, _ => by
      simp only [honS, honSig]
      exact roundPoly_zero_add_one f χ
  | k + 1, r, f, χ, j + 1, h => by
      simp only [honS, honSig]
      exact honS_zero_add_one k _ _ _ j (by omega)

/-- **Lemma 6.4(2)**, pointwise form: `s_{j+1}(a)` is the running value obtained with
`r_{j+1} := a`, i.e. `∑_b f~(r_{≤j}, a, b) χ~(r_{≤j}, a, b)` (with Lemma 6.4(1)). -/
theorem honS_eval_update (k : ℕ) (r : ℕ → F) (f χ : Table F (m + k)) (j : ℕ) (hj : j < k)
    (a : F) : (honS k r f χ j).eval a = honSig k (Function.update r j a) f χ (j + 1) := by
  rw [honS_congr k r (Function.update r j a) f χ j
    (fun i hi => (Function.update_of_ne (by omega) _ _).symm)]
  have := honS_eval k (Function.update r j a) f χ j hj
  rwa [Function.update_self] at this

/-- `honSig` at the first round is `∑_b f(b) χ(b)`. -/
lemma honSig_zero (k : ℕ) (r : ℕ → F) (f χ : Table F (m + k)) :
    honSig k r f χ 0 = ipSum f χ := by
  cases k <;> rfl

/-- After all `k` rounds: `σ_k = ∑_b f_k(b) χ_k(b)` with `f_k = res_{r≤k}(f)`,
`χ_k = res_{r≤k}(χ)`. -/
theorem honSig_last : ∀ (k : ℕ) (r : ℕ → F) (f χ : Table F (m + k)),
    honSig k r f χ k = ipSum (resSeq k r f) (resSeq k r χ)
  | 0, _, _, _ => rfl
  | k + 1, r, f, χ => by
      simp only [honSig, resSeq]
      exact honSig_last k _ _ _

/-- **Lemma 6.4(1):** `f_j(b) = f~(r_{≤j}, b)` for the honest table `f_j = res_{r≤j}(f)`. -/
theorem honest_table {j : ℕ} (r : ℕ → F) (f : Table F (m + j)) (b : Fin m → Bool) :
    resSeq j r f b = mle f (catPt j r (pt b)) :=
  resSeq_eq_mle r f b

/-- **Lemma 6.4(1):** `χ_j(b) = eq((r_{≤j}, b), z)` for `χ_j = res_{r≤j}(χ₀)`. -/
theorem honest_eqTable {j : ℕ} (r : ℕ → F) (z : Fin (m + j) → F) (b : Fin m → Bool) :
    resSeq j r (eqTable z) b = eqv (catPt j r (pt b)) z := by
  rw [resSeq_eq_mle]; exact mle_eqTable z _

/-- Restricting the equality table: `res_a(b ↦ eq(b, (z₀, z'))) = (b' ↦ eq₁(a, z₀) eq(b', z'))`. -/
lemma res_eqTable {k : ℕ} (a z0 : F) (z' : Fin k → F) :
    res a (eqTable (Fin.cons z0 z' : Fin (k + 1) → F)) = eq1 a z0 • eqTable z' := by
  funext b
  have h0 : (pt (Fin.cons false b : Fin (k+1) → Bool) : Fin (k+1) → F) = Fin.cons (bval false) (pt b) := by
    funext i; refine Fin.cases ?_ ?_ i <;> simp [pt]
  have h1 : (pt (Fin.cons true b : Fin (k+1) → Bool) : Fin (k+1) → F) = Fin.cons (bval true) (pt b) := by
    funext i; refine Fin.cases ?_ ?_ i <;> simp [pt]
  simp only [res, eqTable, h0, h1, eqv_cons, Pi.smul_apply, smul_eq_mul, eq1, bval]
  simp only [Bool.false_eq_true, if_false, if_true]
  ring

lemma res_smul {k : ℕ} (a c : F) (f : Table F (k + 1)) : res a (c • f) = c • res a f := by
  funext b; simp only [res, Pi.smul_apply, smul_eq_mul]; ring

lemma resSeq_smul : ∀ (j : ℕ) {k : ℕ} (r : ℕ → F) (c : F) (f : Table F (k + j)),
    resSeq j r (c • f) = c • resSeq j r f
  | 0, _, _, _, _ => rfl
  | j + 1, _, r, c, f => by
      simp only [resSeq]; rw [res_smul, resSeq_smul j]

/-- The restricted equality table: `res_{r≤j}(χ₀)(b) = (∏_{i≤j} eq₁(r_i, z_i)) · eq(b, z_{>j})`
(Lemma 2.5(3)). -/
theorem resSeq_eqTable : ∀ (j : ℕ) {k : ℕ} (r zp : ℕ → F) (zs : Fin k → F),
    resSeq j r (eqTable (catPt j zp zs)) = (∏ i ∈ range j, eq1 (r i) (zp i)) • eqTable zs
  | 0, _, _, _, _ => by funext b; simp [resSeq, catPt]
  | j + 1, k, r, zp, zs => by
      simp only [resSeq, catPt]
      rw [res_eqTable, resSeq_smul, resSeq_eqTable j (shiftSeq r) (shiftSeq zp) zs, smul_smul,
        prod_range_succ' _ j]
      simp only [shiftSeq]
      rw [mul_comm]

/-- `∑_b f(b) eq(b, z) = f~(z)` (Proposition 2.6). -/
theorem ipSum_eqTable {n : ℕ} (f : Table F n) (z : Fin n → F) : ipSum f (eqTable z) = mle f z :=
  rfl

/-- **Lemma 6.4(4):** `∑_b f_0(b) χ_0(b) = f~(z)`. -/
theorem honest_sum_zero {k : ℕ} (r zp : ℕ → F) (zs : Fin m → F) (f : Table F (m + k)) :
    honSig k r f (eqTable (catPt k zp zs)) 0 = mle f (catPt k zp zs) := by
  rw [honSig_zero, ipSum_eqTable]

/-- **Lemma 6.4(4):** `∑_b f_j(b) χ_j(b) = (∏_{i≤j} eq₁(r_i, z_i)) · f_j~(z_{j+1}, …, z_n)`,
here for `j = k` (the number of rounds); every intermediate `j` is this statement for a table
with fewer rounds, by the recursive definition of `honSig`. -/
theorem honest_sum_last {k : ℕ} (r zp : ℕ → F) (zs : Fin m → F) (f : Table F (m + k)) :
    honSig k r f (eqTable (catPt k zp zs)) k =
      (∏ i ∈ range k, eq1 (r i) (zp i)) * mle (resSeq k r f) zs := by
  rw [honSig_last, resSeq_eqTable, ipSum, mle, mul_sum]
  refine sum_congr rfl (fun b _ => ?_)
  simp only [eqTable, Pi.smul_apply, smul_eq_mul]; ring

/-- **Lemma 6.4(4)** for every `j ≤ k`, in the form used by the verifier: with
`f' = res_{r≤j}` applied to a table with `m + j` variables, the running value is
`(∏_{i≤j} eq₁(r_i,z_i)) · f'~(z_{>j})`.  (Same statement as `honest_sum_last`, stated with the
restricted table explicitly.) -/
theorem honest_sum_eq {j : ℕ} (r zp : ℕ → F) (zs : Fin m → F) (f : Table F (m + j)) :
    ipSum (resSeq j r f) (resSeq j r (eqTable (catPt j zp zs))) =
      (∏ i ∈ range j, eq1 (r i) (zp i)) * mle (resSeq j r f) zs := by
  rw [← honSig_last, honest_sum_last]

end Honest

/-! ### The protocol `Π_eval` (§6.2) for a deterministic prover -/

/-- A deterministic prover for `Π_eval` (§6.2, and "Fix a deterministic prover" in §7.3): its
messages as functions of the challenge sequence `r` (`r i` is the paper's `r_{i+1}`).
* `s i r` is the round polynomial `s_{i+1}` (a function of `r_{<i}`, see `Causal`);
* `orc j r` is the oracle `w_j ∈ F^{L_j}` for `1 ≤ j ≤ ℓ-1` (a function of `r_{<j}`; the values
  for other `j` are ignored);
* `g r` is the final table `g : {0,…,N_ℓ-1} → F`, i.e. a table with `m = n - ℓ` variables. -/
structure EvalProver (F : Type*) [Field F] (L : Subgroup Fˣ) (m : ℕ) where
  /-- round polynomials `s_{i+1}` -/
  s : ℕ → (ℕ → F) → F[X]
  /-- oracles `w_j`, `1 ≤ j ≤ ℓ - 1` -/
  orc : (j : ℕ) → (ℕ → F) → (lv L j → F)
  /-- final table `g` -/
  g : (ℕ → F) → Table F m

namespace EvalProver

variable {L : Subgroup Fˣ} {m : ℕ} (P : EvalProver F L m)

/-- The prover's messages are functions of the earlier challenges: `s_{i+1}` of `r_{≤i}` and
`w_j` of `r_{≤j}` (0-based: of `r 0, …, r (i-1)`, resp. `r 0, …, r (j-1)`). -/
def Causal : Prop :=
  (∀ i (r r' : ℕ → F), (∀ k < i, r k = r' k) → P.s i r = P.s i r') ∧
  (∀ j (r r' : ℕ → F), (∀ k < j, r k = r' k) → P.orc j r = P.orc j r')

/-- Round polynomials are elements of `F[X]_{<3}` (they are transmitted as three values). -/
def DegOK : Prop := ∀ i r, (P.s i r).natDegree ≤ 2

variable (ℓ : ℕ) (w0 : L → F)

/-- The oracle words `w_0 = w₀` (the commitment), `w_j = orc j` for `1 ≤ j ≤ ℓ-1`, and
`w_ℓ = ev_{L_ℓ}(G)` with `G = ∑_b g(b) K_b^{(n-ℓ)}`, computed by the verifier. -/
noncomputable def W (r : ℕ → F) : (j : ℕ) → (lv L j → F)
  | 0 => w0
  | j + 1 => if j + 1 = ℓ then ev (lv L (j + 1)) (ofCoords (P.g r)) else P.orc (j + 1) r

/-- The verifier's running values `v_0 = v`, `v_{i+1} = s_{i+1}(r_{i+1})`. -/
noncomputable def vv (v : F) (r : ℕ → F) : ℕ → F
  | 0 => v
  | i + 1 => (P.s i r).eval (r i)

/-- The sumcheck checks `s_j(0) + s_j(1) = v_{j-1}`, `j ∈ [1, ℓ]`. -/
def SumcheckOK (v : F) (r : ℕ → F) : Prop :=
  ∀ i < ℓ, (P.s i r).eval 0 + (P.s i r).eval 1 = P.vv v r i

/-- The closure check `v_ℓ = (∏_j eq₁(r_j, z_j)) · g~(z_{ℓ+1}, …, z_n)`. -/
def ClosureOK (zp : ℕ → F) (zs : Fin m → F) (v : F) (r : ℕ → F) : Prop :=
  P.vv v r ℓ = (∏ i ∈ range ℓ, eq1 (r i) (zp i)) * mle (P.g r) zs

/-- The query check at level `j+1` at the point `η ∈ L_{j+1}`:
`fold_{r_{j+1}}(w_j)(η) = w_{j+1}(η)`. -/
def Chk (r : ℕ → F) (j : ℕ) (η : lv L (j + 1)) : Prop :=
  wfold (r j) (P.W ℓ w0 r j) η = P.W ℓ w0 r (j + 1) η

/-- All query checks for the query point `ξ₀ ∈ L`: for `ℓ ≥ 1`, the checks at levels
`1, …, ℓ` at the points `ξ_j = ξ₀^{2^j}`; for `ℓ = 0`, `w₀(ξ₀) = G(ξ₀)`. -/
def QueryOK (r : ℕ → F) (ξ : L) : Prop :=
  (∀ j < ℓ, P.Chk ℓ w0 r j (ptAt ξ (j + 1))) ∧
  (ℓ = 0 → w0 ξ = (ofCoords (P.g r)).eval ((ξ : Fˣ) : F))

/-- The verifier of `Π_eval` accepts the challenges `r` and the query points `ξ`. -/
def Accepts {κ : ℕ} (zp : ℕ → F) (zs : Fin m → F) (v : F) (r : ℕ → F) (ξ : Fin κ → L) : Prop :=
  P.SumcheckOK ℓ v r ∧ P.ClosureOK ℓ zp zs v r ∧ ∀ t, P.QueryOK ℓ w0 r (ξ t)

end EvalProver

/-- The challenge vector `(r_1, …, r_ℓ) ∈ F^ℓ` as a sequence (`0` beyond `ℓ`). -/
def extR {ℓ : ℕ} (r : Fin ℓ → F) : ℕ → F := fun i => if h : i < ℓ then r ⟨i, h⟩ else 0

lemma extR_update {ℓ : ℕ} (r : Fin ℓ → F) (i : Fin ℓ) (c : F) :
    extR (Function.update r i c) = Function.update (extR r) i c := by
  funext k
  by_cases h : k < ℓ
  · by_cases hk : k = i
    · subst hk
      simp [extR, h]
    · have hne : (⟨k, h⟩ : Fin ℓ) ≠ i := fun e => hk (by rw [← e])
      simp only [extR, h, dif_pos]
      rw [Function.update_of_ne hne, Function.update_of_ne hk]
      simp [extR, h]
  · have hk : k ≠ (i : ℕ) := fun e => h (e ▸ i.isLt)
    rw [Function.update_of_ne hk]
    simp [extR, h]

/-- The acceptance probability of `Π_eval` for a deterministic prover, over the uniform
challenges `(r, ξ) ∈ F^ℓ × L^κ` (§6.2: `Ch_j = F` for `j ≤ ℓ`, `Ch_{ℓ+1} = L^{×κ}`). -/
noncomputable def evalAccProb [Fintype F] {L : Subgroup Fˣ} [Fintype L] {m : ℕ}
    (P : EvalProver F L m) (ℓ κ : ℕ) (w0 : L → F) (zp : ℕ → F) (zs : Fin m → F) (v : F) : ℚ :=
  prob (fun ω : (Fin ℓ → F) × (Fin κ → L) => P.Accepts ℓ w0 zp zs v (extR ω.1) ω.2)

end KBFold
