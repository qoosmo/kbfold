/-
KBFold/LowDegree.lean
Formalisation of §4.4–4.5 of the paper: the general recursion (Lemma 4.5 for arbitrary `t`),
the constant polynomial in kernel coordinates (Lemma 4.12), the low-degree criterion
(Theorem 4.13), Reed–Solomon codes in kernel coordinates (Corollary 4.14), and the evaluation
identity (Proposition 4.15).

Index conventions: the paper's split `b = c + 2^t h` with `c < 2^t`, `h < 2^{n-t}` is
`Fin.append c h : Fin (t + s) → Bool` with `c : Fin t → Bool`, `h : Fin s → Bool`, `n = t + s`
(the first `t` bits are the low-order bits `c`).  The paper's `N - 2^t + c` is
`Fin.append c (fun _ => true)`.
-/
import KBFold.Domain

open Polynomial Finset

namespace KBFold

variable {F : Type*} [Field F]

/-- Hamming weight `wt(b) = ∑_k b_k` (§2.1). -/
def wt {n : ℕ} (b : Fin n → Bool) : ℕ := ∑ k, (if b k then 1 else 0)

lemma wt_cons {n : ℕ} (β : Bool) (b : Fin n → Bool) :
    wt (Fin.cons β b : Fin (n + 1) → Bool) = (if β then 1 else 0) + wt b := by
  simp only [wt, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]

lemma wt_le {n : ℕ} (b : Fin n → Bool) : wt b ≤ n := by
  calc wt b ≤ ∑ _k : Fin n, 1 := Finset.sum_le_sum (fun k _ => by split_ifs <;> simp)
    _ = n := by simp

@[simp] lemma wt_true (n : ℕ) : wt (fun _ : Fin n => true) = n := by simp [wt]

/-! ### Lemma 4.12 (the constant polynomial) -/

/-- The sign table `h ↦ (-1)^{n - wt(h)}` of Lemma 4.12. -/
def signTable (n : ℕ) : Table F n := fun h => (-1) ^ (n - wt h)

lemma ofCoords_zero {n : ℕ} : ofCoords (0 : Table F n) = 0 := by
  simp [ofCoords]

lemma ofCoords_sub {n : ℕ} (f g : Table F n) : ofCoords (f - g) = ofCoords f - ofCoords g := by
  unfold ofCoords; simp [C_sub, sub_mul, Finset.sum_sub_distrib]

/-- Lemma 4.12: `1 = ∑_h (-1)^{n - wt(h)} K_h^{(n)}`. -/
theorem ofCoords_signTable : ∀ n : ℕ, ofCoords (signTable (F := F) n) = 1
  | 0 => by rw [ofCoords_zero_vars]; simp [signTable, wt]
  | n + 1 => by
      rw [ofCoords_split]
      have h1 : (fun b' => signTable (F := F) (n + 1) (Fin.cons true b')) = signTable n := by
        funext b'; simp [signTable, wt_cons, add_comm]
      have h2 : (fun b' => signTable (F := F) (n + 1) (Fin.cons false b')
          + signTable (n + 1) (Fin.cons true b')) = 0 := by
        funext b'
        have := wt_le b'
        simp only [signTable, wt_cons, Bool.false_eq_true, if_false, if_true, zero_add,
          Pi.zero_apply]
        rw [show n + 1 - wt b' = (n - wt b') + 1 by omega, show n + 1 - (1 + wt b') = n - wt b' by
          omega, pow_succ]
        ring
      rw [h1, h2, ofCoords_signTable n, ofCoords_zero]
      simp

/-! ### Lemma 4.5 (recursion), general `t` -/

/-- Lemma 4.5 (recursion): `K^{(t+s)}_{(y,y')}(X) = K^{(t)}_y(X) · K^{(s)}_{y'}(X^{2^t})`. -/
theorem kernel_append {t s : ℕ} (y : Fin t → F) (y' : Fin s → F) :
    kernel (Fin.append y y') = kernel y * expand F (2 ^ t) (kernel y') := by
  unfold kernel
  rw [Fin.prod_univ_add, map_prod]
  congr 1
  · refine Finset.prod_congr rfl (fun k _ => ?_)
    simp [Fin.append_left]
  · refine Finset.prod_congr rfl (fun k _ => ?_)
    simp only [Fin.append_right, Fin.coe_natAdd, map_add, map_pow, expand_X, expand_C]
    rw [← pow_mul, ← pow_add]

lemma pt_append {t s : ℕ} (c : Fin t → Bool) (h : Fin s → Bool) :
    (pt (Fin.append c h) : Fin (t + s) → F) = Fin.append (pt c) (pt h) := by
  funext k
  refine Fin.addCases (fun i => ?_) (fun i => ?_) k <;> simp [pt]

/-- Lemma 4.5 (recursion), Boolean form: `K_{c + 2^t h} = K_c(X) K_h(X^{2^t})`. -/
theorem kernelB_append {t s : ℕ} (c : Fin t → Bool) (h : Fin s → Bool) :
    (kernelB (Fin.append c h) : F[X]) = kernelB c * expand F (2 ^ t) (kernelB h) := by
  rw [kernelB, pt_append, kernel_append]; rfl

/-- The bijection `(c, h) ↦ c + 2^t h` between `B_t × B_s` and `B_{t+s}` (§2.1, splitting
indices). -/
def appendEquiv (t s : ℕ) : (Fin t → Bool) × (Fin s → Bool) ≃ (Fin (t + s) → Bool) where
  toFun p := Fin.append p.1 p.2
  invFun b := (fun i => b (Fin.castAdd s i), fun i => b (Fin.natAdd t i))
  left_inv p := by ext i <;> simp
  right_inv b := Fin.append_castAdd_natAdd

lemma sum_append {M : Type*} [AddCommMonoid M] {t s : ℕ} (g : (Fin (t + s) → Bool) → M) :
    ∑ b, g b = ∑ c, ∑ h, g (Fin.append c h) := by
  rw [← (appendEquiv t s).sum_comp, Fintype.sum_prod_type]; rfl

/-- The decomposition used in the proof of Theorem 4.13:
`U(X) = ∑_c K_c^{(t)}(X) · Y_c(X^{2^t})` with `Y_c = ∑_h λ(c + 2^t h) K_h^{(s)}`. -/
theorem ofCoords_append {t s : ℕ} (lam : Table F (t + s)) :
    ofCoords lam = ∑ c, kernelB c * expand F (2 ^ t) (ofCoords (fun h => lam (Fin.append c h))) := by
  conv_lhs => rw [ofCoords, sum_append]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  simp only [ofCoords, map_sum, Finset.mul_sum, kernelB_append, map_mul, expand_C]
  refine Finset.sum_congr rfl (fun h _ => ?_)
  ring

/-! ### Theorem 4.13 (low-degree criterion) -/

/-- The character condition (4.1) of Theorem 4.13:
`λ(c + 2^t h) = (-1)^{(n-t) - wt(h)} φ(c)` for all `c, h`. -/
def CharCond {t s : ℕ} (lam : Table F (t + s)) (φ : Table F t) : Prop :=
  ∀ c h, lam (Fin.append c h) = (-1) ^ (s - wt h) * φ c

/-- Theorem 4.13, last statement: under (4.1), `U = ∑_c φ(c) K^{(t)}_c`. -/
theorem ofCoords_of_charCond {t s : ℕ} {lam : Table F (t + s)} {φ : Table F t}
    (h : CharCond lam φ) : ofCoords lam = ofCoords φ := by
  rw [ofCoords_append]
  unfold ofCoords
  refine Finset.sum_congr rfl (fun c _ => ?_)
  have : (fun hh => lam (Fin.append c hh)) = fun hh => φ c * signTable s hh := by
    funext hh; rw [h c hh, signTable, mul_comm]
  rw [this, ← ofCoords]
  rw [ofCoords_smul, ofCoords_signTable, mul_one, expand_C, mul_comm]

/-- Theorem 4.13, uniqueness: under (4.1), `φ(c) = λ(c + N - 2^t)`. -/
theorem charCond_phi {t s : ℕ} {lam : Table F (t + s)} {φ : Table F t} (h : CharCond lam φ) :
    φ = fun c => lam (Fin.append c (fun _ => true)) := by
  funext c; rw [h]; simp

/-- Theorem 4.13 (low-degree criterion): for `U = ∑_b λ(b) K_b^{(t+s)}`,
`deg U < 2^t` iff there is `φ` with `λ(c + 2^t h) = (-1)^{s - wt(h)} φ(c)`. -/
theorem lowDegree_iff {t s : ℕ} (lam : Table F (t + s)) :
    ofCoords lam ∈ degreeLT F (2 ^ t) ↔ ∃ φ : Table F t, CharCond lam φ := by
  constructor
  · intro hU
    obtain ⟨φ, hφ, -⟩ := exists_unique_coords (n := t) _ hU
    let lam' : Table F (t + s) := fun b =>
      (-1) ^ (s - wt (fun i => b (Fin.natAdd t i))) * φ (fun i => b (Fin.castAdd s i))
    have hc : CharCond lam' φ := by
      intro c hh; simp [lam']
    have heq : lam = lam' := by
      have h0 : ofCoords (lam - lam') = 0 := by
        rw [ofCoords_sub, ofCoords_of_charCond hc, hφ, sub_self]
      have := ofCoords_eq_zero _ h0
      exact sub_eq_zero.1 this
    exact ⟨φ, heq ▸ hc⟩
  · rintro ⟨φ, hφ⟩
    rw [ofCoords_of_charCond hφ]
    exact ofCoords_mem_degreeLT φ

/-- Theorem 4.13, degree form: `deg U < 2^t` iff (4.1) holds for some `φ`. -/
theorem lowDegree_iff' {t s : ℕ} (lam : Table F (t + s)) :
    (ofCoords lam).degree < 2 ^ t ↔ ∃ φ : Table F t, CharCond lam φ := by
  rw [← lowDegree_iff, mem_degreeLT]; norm_cast

/-! ### Corollary 4.14 (Reed–Solomon codes in kernel coordinates) -/

/-- Corollary 4.14: `RS[L, 2^t] = {ev_L(∑_b λ(b) K_b) : λ satisfies (4.1) for some φ}`
(with `n = t + s` variables).  The paper's hypothesis `M ≥ 2^t` is not needed for this set
equality. -/
theorem RS_eq_charCond (L : Subgroup Fˣ) (t s : ℕ) :
    (RS L (2 ^ t) : Set (L → F)) =
      {w | ∃ lam : Table F (t + s), (∃ φ, CharCond lam φ) ∧ w = ev L (ofCoords lam)} := by
  ext w
  simp only [SetLike.mem_coe, Set.mem_setOf_eq, mem_RS]
  constructor
  · rintro ⟨P, hP, rfl⟩
    have hP' : P ∈ degreeLT F (2 ^ (t + s)) :=
      degreeLT_mono' (Nat.pow_le_pow_right two_pos (Nat.le_add_right t s)) hP
    obtain ⟨lam, hlam, -⟩ := exists_unique_coords (n := t + s) P hP'
    refine ⟨lam, (lowDegree_iff lam).1 (hlam ▸ hP), by rw [hlam]⟩
  · rintro ⟨lam, hφ, rfl⟩
    exact ⟨_, (lowDegree_iff lam).2 hφ, rfl⟩

/-! ### Proposition 4.15 (evaluation identity) -/

/-- Proposition 4.15: `γ_k(ζ) = 2 ζ^{2^{k-1}} + 1` (Lean index `k` is the paper's `k+1`). -/
def gam (ζ : F) (k : ℕ) : F := 2 * ζ ^ (2 ^ k) + 1

/-- Proposition 4.15: `ψ_k(ζ) = (ζ^{2^{k-1}} + 1)/(2 ζ^{2^{k-1}} + 1)`. -/
noncomputable def psi (ζ : F) (k : ℕ) : F := (ζ ^ (2 ^ k) + 1) / (2 * ζ ^ (2 ^ k) + 1)

/-- One factor of the proof of Proposition 4.15: `γ · eq₁(β, ψ) = ζ^{2^{k-1}} + β`. -/
lemma gam_mul_eq1 (a : F) (ha : 2 * a + 1 ≠ 0) (β : Bool) :
    (2 * a + 1) * eq1 (bval β) ((a + 1) / (2 * a + 1)) = a + bval β := by
  have hψ : (2 * a + 1) * ((a + 1) / (2 * a + 1)) = a + 1 := mul_div_cancel₀ _ ha
  cases β <;> simp only [bval, eq1, Bool.false_eq_true, if_true, if_false]
  · linear_combination -hψ
  · linear_combination hψ

/-- Proof of Proposition 4.15: `K_b(ζ) = (∏_k γ_k(ζ)) eq(b, ψ(ζ))`. -/
theorem eval_kernelB {n : ℕ} (ζ : F) (hγ : ∀ k : Fin n, gam ζ k ≠ 0) (b : Fin n → Bool) :
    (kernelB b : F[X]).eval ζ =
      (∏ k : Fin n, gam ζ k) * eqv (pt b) (fun k : Fin n => psi ζ k) := by
  unfold kernelB kernel eqv
  rw [eval_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun k _ => ?_)
  have hk : 2 * ζ ^ (2 ^ (k : ℕ)) + 1 ≠ 0 := hγ k
  simp only [eval_add, eval_pow, eval_X, eval_C, gam, psi, pt]
  rw [gam_mul_eq1 _ hk]

/-- Proposition 4.15 (evaluation identity): if `γ_k(ζ) ≠ 0` for all `k`, then
`U(ζ) = (∏_k γ_k(ζ)) · λ~(ψ(ζ))` for `U = ∑_b λ(b) K_b`. -/
theorem eval_ofCoords {n : ℕ} (lam : Table F n) (ζ : F) (hγ : ∀ k : Fin n, gam ζ k ≠ 0) :
    (ofCoords lam).eval ζ = (∏ k : Fin n, gam ζ k) * mle lam (fun k : Fin n => psi ζ k) := by
  unfold ofCoords mle
  rw [eval_finset_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [eval_mul, eval_C, eval_kernelB ζ hγ]
  ring

end KBFold
