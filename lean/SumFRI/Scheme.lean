/-
SumFRI/Scheme.lean
§5 of the Sum-FRI paper: the encoding (Definition 5.1), the iterated classical folds on the levels
`L_j` (Corollary 4.9), the protocol `Π_eval` for a deterministic prover (§5.2), the honest prover
(Lemma 5.7) and completeness (Theorem 5.8), with the sum protocol `Π_sum` as the case `z = 1`.

Modelling choices are those of `KBFold/Protocol.lean`:
* the number of variables is `n = m + ℓ` (`ℓ` folding rounds, final table with `m` variables);
* the point `z` is given as its first `ℓ` coordinates `zp : ℕ → F` and its last `m` coordinates
  `zs : Fin m → F`, and is `catPt ℓ zp zs`;
* indices are 0-based: challenge `θ i` is the paper's `θ_{i+1}`, the round polynomial `s i` is
  `s_{i+1}`, and the query check `j` is the paper's check at level `j+1`;
* a deterministic prover is given by its messages as functions of the challenges (`SumProver`);
  a round polynomial is modelled as a polynomial of degree `≤ 1` (`DegOK`).
The levels `lv L j`, the points `ptAt`, `extR` and `prob` are those of KBFold.
-/
import SumFRI.Monomial
import KBFold.Protocol

set_option autoImplicit false

open Polynomial Finset

namespace SumFRI

open KBFold

variable {F : Type*} [Field F]

/-! ### Definition 5.1 (encoding) and Corollary 4.9 on the levels `L_j` -/

/-- Definition 5.1: `Enc(f) = ev_L(V_f)`. -/
noncomputable def cEnc (L : Subgroup Fˣ) {n : ℕ} (f : Table F n) : L → F := ev L (vpoly f)

/-- The successive classical folds `cfold_{θ_j}(⋯ cfold_{θ_1}(w))` of a word on `L`. -/
noncomputable def cfoldUp {L : Subgroup Fˣ} (θ : ℕ → F) (w : L → F) : (j : ℕ) → (lv L j → F)
  | 0 => w
  | j + 1 => cwfold (θ j) (cfoldUp θ w j)

/-- The successive classical folds of a polynomial. -/
noncomputable def cfoldUpP (θ : ℕ → F) (U : F[X]) : ℕ → F[X]
  | 0 => U
  | j + 1 => cfold (θ j) (cfoldUpP θ U j)

theorem cfoldSeq_succ' : ∀ (j : ℕ) (θ : ℕ → F) (U : F[X]),
    cfoldSeq (j + 1) θ U = cfold (θ j) (cfoldSeq j θ U)
  | 0, _, _ => rfl
  | j + 1, θ, U => by
      rw [cfoldSeq, cfoldSeq_succ' j (shiftSeq θ) (cfold (θ 0) U)]
      rfl

theorem cfoldUpP_eq_cfoldSeq (θ : ℕ → F) (U : F[X]) : ∀ j, cfoldUpP θ U j = cfoldSeq j θ U
  | 0 => rfl
  | j + 1 => by rw [cfoldUpP, cfoldUpP_eq_cfoldSeq θ U j, cfoldSeq_succ']

/-- Lemma 4.8(4), iterated on the levels. -/
theorem cfoldUp_ev {L : Subgroup Fˣ} (h2 : (2 : F) ≠ 0) (θ : ℕ → F) (U : F[X]) :
    ∀ j, (∀ i < j, (-1 : Fˣ) ∈ lv L i) → cfoldUp θ (ev L U) j = ev (lv L j) (cfoldUpP θ U j)
  | 0, _ => rfl
  | j + 1, h => by
      rw [cfoldUp, cfoldUp_ev h2 θ U j (fun i hi => h i (by omega)), cfoldUpP,
        cwfold_ev (h j (by omega)) h2]
      rfl

/-- **Corollary 4.9 on the levels `L_j`:** for a table `f` with `m + j` variables and `j ≤ μ`,
the `j`-th classical fold of `Enc(f)` is `ev_{L_j}(V_{cres_{θ≤j}(f)})`. -/
theorem cfoldUp_Enc {L : Subgroup Fˣ} {μ : ℕ} (hL : IsSmoothDomain L μ) {m j : ℕ} (hj : j ≤ μ)
    (θ : ℕ → F) (f : Table F (m + j)) :
    cfoldUp θ (cEnc L f) j = ev (lv L j) (vpoly (cresSeq j θ f)) := by
  rcases Nat.eq_zero_or_pos j with rfl | hpos
  · rfl
  rw [cEnc, cfoldUp_ev (two_ne_zero_of_smooth hL (by omega)) θ _ j
    (fun i hi => lv_neg_one_mem hL (by omega)), cfoldUpP_eq_cfoldSeq, cfoldSeq_vpoly]

/-- `cfoldUp θ w j` depends only on `θ_{<j}`. -/
lemma cfoldUp_congr {L : Subgroup Fˣ} (w : L → F) {θ θ' : ℕ → F} :
    ∀ j, (∀ i < j, θ i = θ' i) → cfoldUp θ w j = cfoldUp θ' w j
  | 0, _ => rfl
  | j + 1, h => by
      rw [cfoldUp, cfoldUp, cfoldUp_congr w j (fun i hi => h i (by omega)), h j (by omega)]

/-! ### Lemma 5.7 (honest prover) -/

section Honest

variable {m : ℕ} (zs : Fin m → F)

/-- The honest round polynomials: `hS k θ zp f j` is `s_{j+1}` for the prover started on the
table `f` with `k` variables beyond `m` and the point `(zp_0, …, zp_{k-1}, zs)`, namely
`h_{f_j, z_{>j+1}}(T) = P_{(f_j)_e}(z_{>j+1}) + T P_{(f_j)_o}(z_{>j+1})` with
`f_j = cres_{θ≤j}(f)` (equation (4)). -/
noncomputable def hS : (k : ℕ) → (ℕ → F) → (ℕ → F) → Table F (m + k) → ℕ → F[X]
  | 0, _, _, _, _ => 0
  | k + 1, _, zp, f, 0 =>
      C (rnd0 f (catPt k (shiftSeq zp) zs)) + C (rnd1 f (catPt k (shiftSeq zp) zs)) * X
  | k + 1, θ, zp, f, j + 1 => hS k (shiftSeq θ) (shiftSeq zp) (cres (θ 0) f) j

/-- The honest running values `v_j = P_{f_j}(z_{>j})` (Lemma 5.7). -/
noncomputable def hV : (k : ℕ) → (ℕ → F) → (ℕ → F) → Table F (m + k) → ℕ → F
  | k, _, zp, f, 0 => cpoly f (catPt k zp zs)
  | 0, _, zp, f, _ + 1 => cpoly f (catPt 0 zp zs)
  | k + 1, θ, zp, f, j + 1 => hV k (shiftSeq θ) (shiftSeq zp) (cres (θ 0) f) j

lemma hV_zero (k : ℕ) (θ zp : ℕ → F) (f : Table F (m + k)) :
    hV zs k θ zp f 0 = cpoly f (catPt k zp zs) := by
  cases k <;> rfl

/-- Lemma 5.7(2): `s_j ∈ F[T]_{<2}`. -/
theorem natDegree_hS : ∀ (k : ℕ) (θ zp : ℕ → F) (f : Table F (m + k)) (j : ℕ),
    (hS zs k θ zp f j).natDegree ≤ 1
  | 0, _, _, _, _ => by simp [hS]
  | k + 1, _, zp, f, 0 => by
      simp only [hS]
      rw [add_comm]
      exact natDegree_linear_le
  | k + 1, θ, zp, f, j + 1 => natDegree_hS k _ _ _ j

/-- `s_{j+1}` depends only on `θ_{≤j}` (0-based: `θ 0, …, θ (j-1)`). -/
theorem hS_congr : ∀ (k : ℕ) (θ θ' zp : ℕ → F) (f : Table F (m + k)) (j : ℕ),
    (∀ i < j, θ i = θ' i) → hS zs k θ zp f j = hS zs k θ' zp f j
  | 0, _, _, _, _, _, _ => rfl
  | _ + 1, _, _, _, _, 0, _ => rfl
  | k + 1, θ, θ', zp, f, j + 1, h => by
      simp only [hS]
      rw [h 0 (by omega)]
      exact hS_congr k _ _ _ _ j (fun i hi => h (i + 1) (by omega))

/-- Lemma 5.7(2): `s_{j+1}(θ_{j+1}) = v_{j+1}`. -/
theorem hS_eval : ∀ (k : ℕ) (θ zp : ℕ → F) (f : Table F (m + k)) (j : ℕ), j < k →
    (hS zs k θ zp f j).eval (θ j) = hV zs k θ zp f (j + 1)
  | 0, _, _, _, _, h => absurd h (by omega)
  | k + 1, θ, zp, f, 0, _ => by
      simp only [hS, hV, hV_zero, eval_add, eval_C, eval_mul, eval_X]
      rw [cpoly_cres, ← hround_eq]
      ring
  | k + 1, θ, zp, f, j + 1, h => by
      simp only [hS, hV]
      exact hS_eval k (shiftSeq θ) (shiftSeq zp) (cres (θ 0) f) j (by omega)

/-- Lemma 5.7(2): `s_{j+1}(z_{j+1}) = v_j` (the restriction check of the honest prover). -/
theorem hS_zp : ∀ (k : ℕ) (θ zp : ℕ → F) (f : Table F (m + k)) (j : ℕ), j < k →
    (hS zs k θ zp f j).eval (zp j) = hV zs k θ zp f j
  | 0, _, _, _, _, h => absurd h (by omega)
  | k + 1, θ, zp, f, 0, _ => by
      simp only [hS, eval_add, eval_C, eval_mul, eval_X]
      rw [hV_zero, catPt, ← hround_eq]
      ring
  | k + 1, θ, zp, f, j + 1, h => by
      simp only [hS, hV]
      exact hS_zp k (shiftSeq θ) (shiftSeq zp) (cres (θ 0) f) j (by omega)

/-- After all `k` rounds: `v_k = P_{f_k}(z_{>k}) = P_{cres_{θ≤k}(f)}(zs)`. -/
theorem hV_last : ∀ (k : ℕ) (θ zp : ℕ → F) (f : Table F (m + k)),
    hV zs k θ zp f k = cpoly (cresSeq k θ f) zs
  | 0, _, _, _ => rfl
  | k + 1, θ, zp, f => by
      simp only [hV, cresSeq]
      exact hV_last k _ _ _

end Honest

/-! ### The protocol `Π_eval` (§5.2) for a deterministic prover -/

/-- A deterministic prover for `Π_eval`: its messages as functions of the challenges `θ`
(`θ i` is the paper's `θ_{i+1}`).
* `s i θ` is the round polynomial `s_{i+1}` (a function of `θ_{<i}`, see `Causal`);
* `orc j θ` is the oracle `w_j` for `1 ≤ j ≤ ℓ-1`;
* `g θ` is the final table, with `m = n - ℓ` variables. -/
structure SumProver (F : Type*) [Field F] (L : Subgroup Fˣ) (m : ℕ) where
  /-- round polynomials `s_{i+1}` -/
  s : ℕ → (ℕ → F) → F[X]
  /-- oracles `w_j`, `1 ≤ j ≤ ℓ - 1` -/
  orc : (j : ℕ) → (ℕ → F) → (lv L j → F)
  /-- final table `g` -/
  g : (ℕ → F) → Table F m

namespace SumProver

variable {L : Subgroup Fˣ} {m : ℕ} (P : SumProver F L m)

/-- The prover's messages depend only on the earlier challenges. -/
def Causal : Prop :=
  (∀ i (θ θ' : ℕ → F), (∀ k < i, θ k = θ' k) → P.s i θ = P.s i θ') ∧
  (∀ j (θ θ' : ℕ → F), (∀ k < j, θ k = θ' k) → P.orc j θ = P.orc j θ')

/-- Round polynomials are affine (they are transmitted as two coefficients). -/
def DegOK : Prop := ∀ i θ, (P.s i θ).natDegree ≤ 1

variable (ℓ : ℕ) (w0 : L → F)

/-- The oracle words `w_0 = w₀`, `w_j = orc j` for `1 ≤ j ≤ ℓ-1`, and `w_ℓ = ev_{L_ℓ}(V_g)`,
computed by the verifier. -/
noncomputable def W (θ : ℕ → F) : (j : ℕ) → (lv L j → F)
  | 0 => w0
  | j + 1 => if j + 1 = ℓ then ev (lv L (j + 1)) (vpoly (P.g θ)) else P.orc (j + 1) θ

/-- The verifier's running values `v_0 = v`, `v_{i+1} = s_{i+1}(θ_{i+1})`. -/
noncomputable def vv (v : F) (θ : ℕ → F) : ℕ → F
  | 0 => v
  | i + 1 => (P.s i θ).eval (θ i)

/-- The restriction checks `s_j(z_j) = v_{j-1}`, `j ∈ [1, ℓ]`. -/
def RestrOK (zp : ℕ → F) (v : F) (θ : ℕ → F) : Prop :=
  ∀ i < ℓ, (P.s i θ).eval (zp i) = P.vv v θ i

/-- The closure check `v_ℓ = P_g(z_{ℓ+1}, …, z_n)`. -/
def ClosureOK (zs : Fin m → F) (v : F) (θ : ℕ → F) : Prop :=
  P.vv v θ ℓ = cpoly (P.g θ) zs

/-- The query check at level `j+1` at `η ∈ L_{j+1}`: `cfold_{θ_{j+1}}(w_j)(η) = w_{j+1}(η)`. -/
def Chk (θ : ℕ → F) (j : ℕ) (η : lv L (j + 1)) : Prop :=
  cwfold (θ j) (P.W ℓ w0 θ j) η = P.W ℓ w0 θ (j + 1) η

/-- All query checks for the query point `ξ₀ ∈ L`. -/
def QueryOK (θ : ℕ → F) (ξ : L) : Prop :=
  (∀ j < ℓ, P.Chk ℓ w0 θ j (ptAt ξ (j + 1))) ∧
  (ℓ = 0 → w0 ξ = (vpoly (P.g θ)).eval ((ξ : Fˣ) : F))

/-- The verifier of `Π_eval` accepts the challenges `θ` and the query points `ξ`. -/
def Accepts {κ : ℕ} (zp : ℕ → F) (zs : Fin m → F) (v : F) (θ : ℕ → F) (ξ : Fin κ → L) : Prop :=
  P.RestrOK ℓ zp v θ ∧ P.ClosureOK ℓ zs v θ ∧ ∀ t, P.QueryOK ℓ w0 θ (ξ t)

end SumProver

/-- The acceptance probability of `Π_eval` over the uniform challenges `(θ, ξ) ∈ F^ℓ × L^κ`. -/
noncomputable def sumAccProb [Fintype F] {L : Subgroup Fˣ} [Fintype L] {m : ℕ}
    (P : SumProver F L m) (ℓ κ : ℕ) (w0 : L → F) (zp : ℕ → F) (zs : Fin m → F) (v : F) : ℚ :=
  prob (fun ω : (Fin ℓ → F) × (Fin κ → L) => P.Accepts ℓ w0 zp zs v (extR ω.1) ω.2)

/-! ### Theorem 5.8 (completeness) -/

/-- The honest prover of §5.2 for the table `f` (with `n = m + ℓ` variables) and the point
`z = (zp_0, …, zp_{ℓ-1}, zs)`. -/
noncomputable def honestProver (L : Subgroup Fˣ) {m ℓ : ℕ} (f : Table F (m + ℓ)) (zp : ℕ → F)
    (zs : Fin m → F) : SumProver F L m where
  s i θ := hS zs ℓ θ zp f i
  orc j θ := cfoldUp θ (cEnc L f) j
  g θ := cresSeq ℓ θ f

section

variable {L : Subgroup Fˣ} {m ℓ : ℕ} (f : Table F (m + ℓ)) (zp : ℕ → F) (zs : Fin m → F)

theorem honestProver_causal : (honestProver L f zp zs).Causal :=
  ⟨fun i θ θ' h => hS_congr zs ℓ θ θ' zp f i h, fun j _ _ h => cfoldUp_congr _ j h⟩

theorem honestProver_degOK : (honestProver L f zp zs).DegOK :=
  fun i θ => natDegree_hS zs ℓ θ zp f i

/-- The honest oracles are the successive classical folds of `Enc(f)`, and so is `w_ℓ`. -/
theorem honest_W {μ : ℕ} (hL : IsSmoothDomain L μ) (hℓ : ℓ ≤ μ) (θ : ℕ → F) :
    ∀ j ≤ ℓ, (honestProver L f zp zs).W ℓ (cEnc L f) θ j = cfoldUp θ (cEnc L f) j
  | 0, _ => rfl
  | j + 1, hj => by
      simp only [SumProver.W]
      split_ifs with h
      · subst h
        rw [cfoldUp_Enc hL hℓ θ f]
        rfl
      · rfl

/-- The verifier's running values equal the honest values `v_j = P_{f_j}(z_{>j})`. -/
theorem honest_vv (θ : ℕ → F) :
    ∀ j ≤ ℓ, (honestProver L f zp zs).vv (cpoly f (catPt ℓ zp zs)) θ j = hV zs ℓ θ zp f j
  | 0, _ => (hV_zero zs ℓ θ zp f).symm
  | j + 1, hj => hS_eval zs ℓ θ zp f j (by omega)

/-- The honest prover passes every check, for every `θ` and `ξ` (proof of Theorem 5.8). -/
theorem honest_accepts {μ : ℕ} (hL : IsSmoothDomain L μ) (hℓ : ℓ ≤ μ) {κ : ℕ} (θ : ℕ → F)
    (ξ : Fin κ → L) :
    (honestProver L f zp zs).Accepts ℓ (cEnc L f) zp zs (cpoly f (catPt ℓ zp zs)) θ ξ := by
  refine ⟨?_, ?_, ?_⟩
  · -- restriction
    intro i hi
    rw [honest_vv f zp zs θ i hi.le]
    exact hS_zp zs ℓ θ zp f i hi
  · -- closure
    unfold SumProver.ClosureOK
    rw [honest_vv f zp zs θ ℓ le_rfl, hV_last]
    rfl
  · -- queries
    intro t
    refine ⟨?_, ?_⟩
    · intro j hj
      unfold SumProver.Chk
      rw [honest_W f zp zs hL hℓ θ j hj.le, honest_W f zp zs hL hℓ θ (j + 1) hj]
      rfl
    · intro h0
      subst h0
      rfl

/-- **Theorem 5.8 (completeness).** If `w₀ = Enc(f)`, `v = P_f(z)` and the prover is honest, the
verifier accepts with probability `1`. -/
theorem completeness [Fintype F] [Fintype L] {μ : ℕ} (hL : IsSmoothDomain L μ) (hℓ : ℓ ≤ μ)
    (κ : ℕ) :
    sumAccProb (honestProver L f zp zs) ℓ κ (cEnc L f) zp zs (cpoly f (catPt ℓ zp zs)) = 1 := by
  unfold sumAccProb
  have : (fun ω : (Fin ℓ → F) × (Fin κ → L) =>
      (honestProver L f zp zs).Accepts ℓ (cEnc L f) zp zs (cpoly f (catPt ℓ zp zs))
        (extR ω.1) ω.2) = fun _ => True := by
    funext ω
    simp only [eq_iff_iff, iff_true]
    exact honest_accepts f zp zs hL hℓ (extR ω.1) ω.2
  rw [this]
  haveI : Nonempty L := ⟨1⟩
  exact prob_true

end

/-! ### The sum protocol `Π_sum` -/

/-- The point `(1, …, 1)`. -/
lemma catPt_one : ∀ (j : ℕ) {m : ℕ}, catPt j (fun _ => (1 : F)) (fun _ : Fin m => 1) = fun _ => 1
  | 0, _ => rfl
  | j + 1, m => by
      simp only [catPt]
      have hs : shiftSeq (fun _ : ℕ => (1 : F)) = fun _ => 1 := rfl
      rw [hs, catPt_one j]
      funext i
      refine Fin.cases ?_ (fun i => ?_) i <;> simp

/-- **Theorem 5.8 for `Π_sum`:** with `z = (1, …, 1)` and `v = ∑_a f(a)`, the honest prover is
accepted with probability `1`. -/
theorem completeness_sum [Fintype F] {L : Subgroup Fˣ} [Fintype L] {m ℓ : ℕ}
    (f : Table F (m + ℓ)) {μ : ℕ} (hL : IsSmoothDomain L μ) (hℓ : ℓ ≤ μ) (κ : ℕ) :
    sumAccProb (honestProver L f (fun _ => 1) (fun _ => 1)) ℓ κ (cEnc L f) (fun _ => 1)
      (fun _ => 1) (∑ a, f a) = 1 := by
  rw [← cpoly_one f, ← catPt_one ℓ]
  exact completeness f _ _ hL hℓ κ

end SumFRI
