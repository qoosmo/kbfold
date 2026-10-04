/-
SumFRI/RBR.lean
§6.6 of the Sum-FRI paper: round-by-round knowledge soundness of `Π_eval`
(unique-decoding regime).
* Definition 6.17 (doomed set and extractor): `cNotDoomed`, `cDoomed`, `cExt`, with the
  auxiliary objects of §6.6 (`cwhat` = `ŵ_j`, `cWset` = `𝒲_j(c)`, `cdens`,
  `csigmaJ` = `σ_j(c) = P_{λ[c]}(z_{>j})`, the restriction checks `RestrT`);
* Lemma 6.18 (one round of the chain) `crbr_step`;
* Lemma 6.19 (restriction step for a codeword): the generic round polynomial `sRC`
  (`sRC_eval`, `sRC_eval_cres`), the coefficient vector of a folded codeword `ccoeffs_cwfold`,
  and the instance at level `j` (`csRw`, `csRw_zp`, `csRw_eval`);
* Theorem 6.20 items 1–3: `crbr_round_one`, `crbr_round`, `crbr_final`;
* Proposition 6.22 (`ℓ = 0`): `crbr_l0`.

Partial transcripts are modelled as in `KBFold/RBR.lean` (`PTrans`, `PTrans.updR`, `Wd`, `vvT`,
`zfull` are reused): the data `τ` holds the round polynomials `τ.s i` (`s_{i+1}`), the oracles
`τ.w j` and the challenges `τ.r i` (`θ_{i+1}`).  Round polynomials are required to lie in
`F[X]_{<2}`.  The connection with the generic transcript model (Theorem 6.20, "Consequently")
is in `SumFRI/RBRGeneric.lean`.
-/
import SumFRI.Soundness
import KBFold.RBR

set_option autoImplicit false

open Polynomial Finset

namespace SumFRI

open KBFold

variable {F : Type*} [Field F]

/-! ### Lemma 6.19 (restriction step for a codeword), generic form -/

section RoundPolyC

/-- The round polynomial `h_{λ, z'}(T) = P_{λ_e}(z') + T P_{λ_o}(z')` of a table `λ` with
`k+1` variables (Definition 4.10). -/
noncomputable def sRC {k : ℕ} (lam : Table F (k + 1)) (z' : Fin k → F) : F[X] :=
  C (rnd0 lam z') + C (rnd1 lam z') * X

theorem natDegree_sRC {k : ℕ} (lam : Table F (k + 1)) (z' : Fin k → F) :
    (sRC lam z').natDegree ≤ 1 := by
  unfold sRC
  rw [add_comm]
  exact natDegree_linear_le

/-- Lemma 4.11(1): `h_{λ,z'}(t) = P_λ(t, z')`. -/
theorem sRC_eval {k : ℕ} (lam : Table F (k + 1)) (z' : Fin k → F) (t : F) :
    (sRC lam z').eval t = cpoly lam (Fin.cons t z') := by
  simp only [sRC, eval_add, eval_C, eval_mul, eval_X]
  rw [← hround_eq]
  ring

/-- Lemma 4.11(1): `h_{λ,z'}(t) = P_{cres_t(λ)}(z')`. -/
theorem sRC_eval_cres {k : ℕ} (lam : Table F (k + 1)) (z' : Fin k → F) (t : F) :
    (sRC lam z').eval t = cpoly (cres t lam) z' := by
  rw [sRC_eval, cpoly_cres]

variable {D : Subgroup Fˣ}

/-- Lemma 4.8(4): `P_{cfold_θ(c)} = cfold_θ(P_c)` for `c ∈ RS[D, 2d]`. -/
theorem polyOf_cwfold [Finite D] [Finite (sqDom D)] (hD : (-1 : Fˣ) ∈ D) (h2 : (2 : F) ≠ 0)
    (θ : F) {d : ℕ} (hd : 2 * d ≤ Nat.card D) (hd' : d ≤ Nat.card (sqDom D)) {c : D → F}
    (hc : c ∈ RS D (2 * d)) : polyOf (cwfold θ c) = cfold θ (polyOf c) := by
  obtain ⟨hP, hPc⟩ := polyOf_spec hd hc
  apply polyOf_unique hd' (cfold_mem_degreeLT θ hP)
  rw [← cwfold_ev hD h2, hPc]

/-- Lemma 4.8(4) and Theorem 4.6: the coefficient vector of `cfold_θ(c)` is
`cres_θ(λ[c])`. -/
theorem ccoeffs_cwfold [Finite D] (hD : (-1 : Fˣ) ∈ D) (h2 : (2 : F) ≠ 0)
    {k : ℕ} (hk : 2 * 2 ^ k ≤ Nat.card D) (hk' : 2 ^ k ≤ Nat.card (sqDom D)) {c : D → F}
    (hc : c ∈ RS D (2 * 2 ^ k)) (θ : F) :
    ccoeffs k (polyOf (cwfold θ c)) = cres θ (ccoeffs (k + 1) (polyOf c)) := by
  haveI : Finite (sqDom D) := sqDom_finite
  rw [polyOf_cwfold hD h2 θ hk hk' hc]
  have hP : polyOf c ∈ degreeLT F (2 ^ (k + 1)) := by
    rw [pow_succ']; exact (polyOf_spec hk hc).1
  conv_lhs => rw [← vpoly_ccoeffs hP]
  rw [cfold_vpoly, ccoeffs_vpoly]

/-- Transport of `P_λ(x)` along an equality of numbers of variables. -/
lemma cpoly_ccoeffs_congr (P : F[X]) {a b : ℕ} (h : a = b) (x : Fin a → F) (y : Fin b → F)
    (hxy : ∀ i : Fin b, x (Fin.cast h.symm i) = y i) :
    cpoly (ccoeffs a P) x = cpoly (ccoeffs b P) y := by
  subst h
  congr 1
  funext i
  exact hxy i

end RoundPolyC

/-! ### Definition 6.17 (doomed set and extractor) -/

section Doomed

variable {L : Subgroup Fˣ} {m : ℕ} (ℓ : ℕ) (w0 : L → F) (zp : ℕ → F) (zs : Fin m → F) (v : F)
  (δ : ℚ)

/-- `ŵ_{j+1} = cfold_{θ_{j+1}}(w_j) ∈ F^{L_{j+1}}` (§6.6, "Notation"). -/
noncomputable def cwhat (τ : PTrans F L) (j : ℕ) : lv L (j + 1) → F :=
  cwfold (τ.r j) (Wd w0 τ j)

/-- The witness sets (§6.6): `𝒲_0(c) = {ξ ∈ L : w₀(±ξ) = c(±ξ)}` and, for `j ≥ 1`,
`𝒲_j(c) = {ξ ∈ L : ξ^{2^i} ∉ ℬ_i for i ∈ [1, j-1], and ŵ_j(ξ^{2^j}) = c(ξ^{2^j})}`. -/
def cWset (τ : PTrans F L) : (j : ℕ) → (lv L j → F) → Set L
  | 0, c => {ξ | w0 ξ = c ξ ∧ w0 (negPt ξ) = c (negPt ξ)}
  | j + 1, c => {ξ | (∀ i < j, cwhat w0 τ i (ptAt ξ (i + 1)) = Wd w0 τ (i + 1) (ptAt ξ (i + 1))) ∧
      cwhat w0 τ j (ptAt ξ (j + 1)) = c (ptAt ξ (j + 1))}

/-- `dens_j(c) = |𝒲_j(c)| / M`. -/
noncomputable def cdens (τ : PTrans F L) (j : ℕ) (c : lv L j → F) : ℚ :=
  ((cWset w0 τ j c).ncard : ℚ) / Nat.card L

/-- `σ_j(c) = P_{λ[c]}(z_{j+1}, …, z_n)`, with `λ[c]` the coefficient vector (with `n - j`
variables) of `P_c`.  It does not depend on the challenges. -/
noncomputable def csigmaJ (j : ℕ) (c : lv L j → F) : F :=
  cpoly (ccoeffs (m + ℓ - j) (polyOf c)) (fun i => zfull ℓ zp zs (j + i))

/-- The restriction checks `s_i(z_i) = v_{i-1}` of indices `1, …, j`. -/
def RestrT (τ : PTrans F L) (j : ℕ) : Prop :=
  ∀ i < j, (τ.s i).eval (zp i) = vvT v τ i

/-- **Definition 6.17:** for `j ∈ [1, ℓ]`, `τ_j` is *not doomed* iff the restriction checks of
indices `1, …, j` hold and some `c ∈ 𝒞_j` has `dens_j(c) ≥ 1-δ` and `v_j = σ_j(c)`. -/
def cNotDoomed (τ : PTrans F L) (j : ℕ) : Prop :=
  RestrT zp v τ j ∧ ∃ c ∈ RS (lv L j) (Nd m ℓ j), 1 - δ ≤ cdens w0 τ j c ∧
    vvT v τ j = csigmaJ ℓ zp zs j c

/-- **Definition 6.17:** `τ_0` is doomed, and `τ_j` (`1 ≤ j ≤ ℓ`) is doomed iff it is not
"not doomed".  (A full transcript is doomed iff the verifier rejects it; see `cFullAccepts`.) -/
def cDoomed (τ : PTrans F L) (j : ℕ) : Prop := j = 0 ∨ ¬ cNotDoomed ℓ w0 zp zs v δ τ j

/-- The prover whose messages are those of `τ` (and final table `g`). -/
def cproverOf (τ : PTrans F L) (g : Table F m) : SumProver F L m :=
  ⟨fun i _ => τ.s i, fun j _ => τ.w j, fun _ => g⟩

/-- The verifier accepts the full transcript `(τ, g, ξ)`. -/
def cFullAccepts {κ : ℕ} (τ : PTrans F L) (g : Table F m) (ξ : Fin κ → L) : Prop :=
  (cproverOf τ g).Accepts ℓ w0 zp zs v τ.r ξ

/-- The relation `R^δ_eval` with `dist = Δ^fib₀` (§6.6, "Relation"): `f` is a witness for
`(w₀; z, v)` iff `Δ^fib₀(w₀, Enc(f)) ≤ δ` and `P_f(z) = v`. -/
def cIsWitness (f : Table F (m + ℓ)) : Prop :=
  fibDist w0 (cEnc L f) ≤ δ ∧ cpoly f (catPt ℓ zp zs) = v

/-- **Definition 6.17 (extractor):** the decoded table of `w₀` if `Δ^fib₀(w₀, 𝒞₀) ≤ δ`, and the
zero table otherwise. -/
noncomputable def cExt : Table F (m + ℓ) := by
  classical exact
    if FibDistLE w0 (RS L (2 ^ (m + ℓ)) : Set (L → F)) δ then cdecTable L (m + ℓ) δ w0 else 0

/-- The output of `cExt` is a witness if `Δ^fib₀(w₀, 𝒞₀) ≤ δ` and `P_{f*}(z) = v`. -/
theorem cExt_witness_of {R : ℕ} (hL : IsSmoothDomain L (m + ℓ + R))
    (hF : FibDistLE w0 (RS L (2 ^ (m + ℓ)) : Set (L → F)) δ)
    (hv : cpoly (cdecTable L (m + ℓ) δ w0) (catPt ℓ zp zs) = v) :
    cIsWitness ℓ w0 zp zs v δ (cExt ℓ w0 δ) := by
  classical
  haveI := hL.finite
  have hE : cExt ℓ w0 δ = cdecTable L (m + ℓ) δ w0 := by simp [cExt, hF]
  rw [cIsWitness, hE, cdecTable_spec (show 2 ^ (m + ℓ) ≤ Nat.card L from
    Nd_le_card hL (j := 0) (by omega)) hF]
  exact ⟨(dec_spec hF).2, hv⟩

end Doomed

/-! ### Congruence: `τ_j` only depends on `θ_{≤ j}` -/

section Congr

variable {L : Subgroup Fˣ} {m : ℕ} {ℓ : ℕ} {w0 : L → F} {zp : ℕ → F} {zs : Fin m → F} {v : F}
  {δ : ℚ}

lemma cwhat_updR_lt (τ : PTrans F L) {j i : ℕ} (c : F) (hi : i < j) :
    cwhat w0 (τ.updR j c) i = cwhat w0 τ i := by
  simp only [cwhat]
  rw [Wd_updR]
  simp only [PTrans.updR, Function.update_of_ne (show i ≠ j by omega)]

lemma cwhat_updR_eq (τ : PTrans F L) (j : ℕ) (c : F) :
    cwhat w0 (τ.updR j c) j = cwfold c (Wd w0 τ j) := by
  simp only [cwhat]
  rw [Wd_updR]
  simp only [PTrans.updR, Function.update_self]

lemma cWset_updR (τ : PTrans F L) (j : ℕ) (c : F) (c' : lv L j → F) :
    cWset w0 (τ.updR j c) j c' = cWset w0 τ j c' := by
  cases j with
  | zero => rfl
  | succ k =>
    ext ξ
    simp only [cWset, Set.mem_setOf_eq, Wd_updR]
    rw [cwhat_updR_lt τ c (by omega : k < k + 1)]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨fun i hi => by rw [← cwhat_updR_lt τ c (by omega : i < k + 1)]; exact h1 i hi, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨fun i hi => by rw [cwhat_updR_lt τ c (by omega : i < k + 1)]; exact h1 i hi, h2⟩

/-- `τ_j` does not depend on the challenge `θ_{j+1}`. -/
theorem cNotDoomed_updR (τ : PTrans F L) (j : ℕ) (c : F) :
    cNotDoomed ℓ w0 zp zs v δ (τ.updR j c) j ↔ cNotDoomed ℓ w0 zp zs v δ τ j := by
  simp only [cNotDoomed, RestrT, cdens, cWset_updR, vvT_updR τ j c j le_rfl]
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

/-! ### Lemma 6.18 (one round of the chain) -/

section Step

variable {L : Subgroup Fˣ} {m : ℕ} {ℓ : ℕ} {w0 : L → F} {δ : ℚ}

/-- **Lemma 6.18 (one round of the chain).** Let `j < ℓ` (the paper's round `j+1`), and let
`θ_{j+1}` be good for `w_j`.  If `c' ∈ 𝒞_{j+1}` has `dens_{j+1}(c') ≥ 1-δ`, then
`Δ^fib_j(w_j, 𝒞_j) ≤ δ`, the codeword `c = dec_j(w_j)` satisfies `cfold_{θ_{j+1}}(c) = c'`, and
`𝒲_{j+1}(c') ⊆ 𝒲_j(c)`. -/
theorem crbr_step {R : ℕ} (hL : IsSmoothDomain L (m + ℓ + R)) (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2)
    (τ : PTrans F L) {j : ℕ} (hj : j < ℓ) (hgood : cGoodAt ℓ δ m j (Wd w0 τ j) (τ.r j))
    (c' : lv L (j + 1) → F) (hc' : c' ∈ RS (lv L (j + 1)) (Nd m ℓ (j + 1)))
    (hdens : 1 - δ ≤ cdens w0 τ (j + 1) c') :
    FibDistLE (Wd w0 τ j) (RS (lv L j) (2 * Nd m ℓ (j + 1)) : Set _) δ ∧
      cwfold (τ.r j) (cdecAt ℓ δ m j (Wd w0 τ j)) = c' ∧
      cWset w0 τ (j + 1) c' ⊆ cWset w0 τ j (cdecAt ℓ δ m j (Wd w0 τ j)) := by
  obtain ⟨hDj, hμj, hdD, hrate⟩ := level_facts hL hj
  have hδj : δ ≤ (1 - rate (sqDom (lv L j)) (Nd m ℓ (j + 1))) / 2 := by rw [hrate]; exact hδ
  haveI := hL.finite
  haveI : Finite (sqDom (lv L j)) := lv_finite (L := L) (j + 1)
  haveI := lv_finite (L := L) (j + 1)
  set Y := agreeSet (cwhat w0 τ j) c'
  have hsubY : cWset w0 τ (j + 1) c' ⊆ (fun ξ : L => ptAt ξ (j + 1)) ⁻¹' Y := by
    intro ξ hξ; exact hξ.2
  have hcardW : (cWset w0 τ (j + 1) c').ncard ≤ 2 ^ (j + 1) * Y.ncard := by
    rw [← ncard_preimage_ptAt hL (j + 1) (by omega) Y]
    exact Set.ncard_le_ncard hsubY (Set.toFinite _)
  have hML : Nat.card L = 2 ^ (j + 1) * Nat.card (lv L (j + 1)) := by
    rw [show Nat.card L = Nat.card (lv L 0) from rfl, card_lv hL (by omega),
      card_lv hL (by omega), ← pow_add]
    congr 1; omega
  have hLpos : (0 : ℚ) < Nat.card L := by
    haveI : Nonempty L := ⟨1⟩; exact_mod_cast Nat.card_pos
  have hY : (1 - δ) * Nat.card (sqDom (lv L j)) ≤ Y.ncard := by
    have h1 : (1 - δ) * Nat.card L ≤ (cWset w0 τ (j + 1) c').ncard := by
      rw [cdens, le_div_iff₀ hLpos] at hdens; exact hdens
    have h2 : ((cWset w0 τ (j + 1) c').ncard : ℚ) ≤ 2 ^ (j + 1) * Y.ncard := by
      exact_mod_cast hcardW
    rw [hML] at h1
    push_cast at h1
    have h3 : (0 : ℚ) < 2 ^ (j + 1) := by positivity
    have : (1 - δ) * Nat.card (lv L (j + 1)) ≤ Y.ncard := by nlinarith
    exact this
  obtain ⟨hF, hfold, hagree⟩ := cone_step hDj hμj hδj (Wd w0 τ j) (τ.r j) hgood c' hc' hY
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

/-! ### Lemma 6.19 at level `j` and Theorem 6.20 -/

section Theorem

variable {L : Subgroup Fˣ} {m : ℕ} {ℓ : ℕ} {w0 : L → F} {zp : ℕ → F} {zs : Fin m → F} {v : F}
  {δ : ℚ}

variable (ℓ w0 zp zs δ) in
/-- **Lemma 6.19 at level `j`** (the paper's round `j+1`): the round polynomial
`s^c_{j+1} = h_{λ[c], z_{>j+1}}` for the codeword `c = dec_j(w_j)`. -/
noncomputable def csRw (τ : PTrans F L) (j : ℕ) : F[X] :=
  sRC (ccoeffs (m + ℓ - (j + 1) + 1) (polyOf (cdecAt ℓ δ m j (Wd w0 τ j))))
    (fun i => zfull ℓ zp zs (j + 1 + i))

lemma csRw_updR (τ : PTrans F L) (j : ℕ) (c : F) :
    csRw ℓ w0 zp zs δ (τ.updR j c) j = csRw ℓ w0 zp zs δ τ j := by
  simp only [csRw, Wd_updR]

/-- **Lemma 6.19 at level `j`**, first claim, in the form `s^c(z_{j+1}) = σ_j(c)`. -/
theorem csRw_zfull (τ : PTrans F L) {j : ℕ} (hj : j < ℓ) :
    (csRw ℓ w0 zp zs δ τ j).eval (zfull ℓ zp zs j) =
      csigmaJ ℓ zp zs j (cdecAt ℓ δ m j (Wd w0 τ j)) := by
  rw [csRw, sRC_eval, csigmaJ]
  refine (cpoly_ccoeffs_congr _ (show m + ℓ - j = m + ℓ - (j + 1) + 1 by omega) _ _ ?_).symm
  intro i
  refine Fin.cases ?_ (fun i' => ?_) i
  · simp
  · simp only [Fin.cons_succ, Fin.coe_cast, Fin.val_succ]
    congr 1; omega

/-- **Lemma 6.19(1) at level `j`:** `s^c(z_{j+1}) = σ_j(c)`. -/
theorem csRw_zp (τ : PTrans F L) {j : ℕ} (hj : j < ℓ) :
    (csRw ℓ w0 zp zs δ τ j).eval (zp j) = csigmaJ ℓ zp zs j (cdecAt ℓ δ m j (Wd w0 τ j)) := by
  rw [← zfull_lt zp zs hj]
  exact csRw_zfull τ hj

/-- **Lemma 6.19(2) at level `j`:** `s^c(a) = σ_{j+1}(cfold_a(c))`, for `c = dec_j(w_j) ∈ 𝒞_j`. -/
theorem csRw_eval {R : ℕ} (hL : IsSmoothDomain L (m + ℓ + R)) (τ : PTrans F L) {j : ℕ}
    (hj : j < ℓ) (hc : cdecAt ℓ δ m j (Wd w0 τ j) ∈ RS (lv L j) (2 * Nd m ℓ (j + 1))) (a : F) :
    (csRw ℓ w0 zp zs δ τ j).eval a =
      csigmaJ ℓ zp zs (j + 1) (cwfold a (cdecAt ℓ δ m j (Wd w0 τ j))) := by
  obtain ⟨hDj, hμj, hdD, -⟩ := level_facts hL hj
  haveI := hL.finite
  haveI := lv_finite (L := L) j
  have hneg := lv_neg_one_mem hL (j := j) (by omega)
  have h2F := two_ne_zero_of_smooth hL (by omega : 1 ≤ m + ℓ + R)
  have hk' : 2 ^ (m + ℓ - (j + 1)) ≤ Nat.card (sqDom (lv L j)) :=
    Nd_le_card hL (j := j + 1) (by omega)
  rw [csRw, sRC_eval_cres, csigmaJ, ccoeffs_cwfold hneg h2F hdD hk' hc a]

variable (ℓ w0 zp zs δ) in
/-- The bad challenges of round `j+1` (proof of Theorem 6.20, items 1 and 2): `θ_{j+1}` is not
good for `w_j`, or `Δ^fib_j(w_j, 𝒞_j) ≤ δ`, `s_{j+1} ≠ s^c_{j+1}` and
`s_{j+1}(θ_{j+1}) = s^c_{j+1}(θ_{j+1})`. -/
def cBadR (τ : PTrans F L) (j : ℕ) (a : F) : Prop :=
  ¬ cGoodAt ℓ δ m j (Wd w0 τ j) a ∨
    (FibDistLE (Wd w0 τ j) (RS (lv L j) (2 * Nd m ℓ (j + 1)) : Set _) δ ∧
      τ.s j ≠ csRw ℓ w0 zp zs δ τ j ∧ (τ.s j).eval a = (csRw ℓ w0 zp zs δ τ j).eval a)

/-- At most `M_{j+1} + 1` challenges are bad (Lemmas 6.9 and 4.11(3)). -/
theorem card_cBadR [Fintype F] [DecidableEq F] {R : ℕ} (hL : IsSmoothDomain L (m + ℓ + R))
    (hδ0 : 0 < δ) (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2) (τ : PTrans F L) {j : ℕ} (hj : j < ℓ)
    (hdeg : (τ.s j).natDegree ≤ 1) :
    ({a : F | cBadR ℓ w0 zp zs δ τ j a}.ncard : ℚ) ≤ Nat.card (lv L (j + 1)) + 1 := by
  classical
  have hset : {a : F | cBadR ℓ w0 zp zs δ τ j a} =
      {a : F | ¬ cGoodAt ℓ δ m j (Wd w0 τ j) a} ∪
      {a : F | FibDistLE (Wd w0 τ j) (RS (lv L j) (2 * Nd m ℓ (j + 1)) : Set _) δ ∧
        τ.s j ≠ csRw ℓ w0 zp zs δ τ j ∧ (τ.s j).eval a = (csRw ℓ w0 zp zs δ τ j).eval a} := by
    ext a; simp only [cBadR, Set.mem_setOf_eq, Set.mem_union]
  rw [hset]
  refine (Nat.cast_le.2 (Set.ncard_union_le _ _)).trans ?_
  push_cast
  apply add_le_add
  · exact_mod_cast card_cbadFold_le hL hδ0 hδ hj _
  · by_cases h : FibDistLE (Wd w0 τ j) (RS (lv L j) (2 * Nd m ℓ (j + 1)) : Set _) δ ∧
        τ.s j ≠ csRw ℓ w0 zp zs δ τ j
    · have e : {a : F | FibDistLE (Wd w0 τ j) (RS (lv L j) (2 * Nd m ℓ (j + 1)) : Set _) δ ∧
          τ.s j ≠ csRw ℓ w0 zp zs δ τ j ∧ (τ.s j).eval a = (csRw ℓ w0 zp zs δ τ j).eval a} =
          {a : F | (τ.s j).eval a = (csRw ℓ w0 zp zs δ τ j).eval a} := by
        ext a; simp [h.1, h.2]
      rw [e, ← card_filter_eq_ncard]
      exact_mod_cast card_agree_le_one _ _ h.2 hdeg (natDegree_sRC _ _)
    · have e : {a : F | FibDistLE (Wd w0 τ j) (RS (lv L j) (2 * Nd m ℓ (j + 1)) : Set _) δ ∧
          τ.s j ≠ csRw ℓ w0 zp zs δ τ j ∧ (τ.s j).eval a = (csRw ℓ w0 zp zs δ τ j).eval a} = ∅ := by
        ext a
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        exact fun h' => h ⟨h'.1, h'.2.1⟩
      rw [e]; simp

/-- Core of the proof of Theorem 6.20, items 1 and 2: if `θ_{j+1} = a` is not bad and
`τ_{j+1}` is not doomed, then `Δ^fib_j(w_j, 𝒞_j) ≤ δ`, and `τ_j` satisfies the conditions of
Definition 6.17 with `c = dec_j(w_j)` (restriction checks `1..j`, `dens_j(c) ≥ 1-δ`,
`v_j = σ_j(c)`). -/
theorem crbr_escape {R : ℕ} (hL : IsSmoothDomain L (m + ℓ + R)) (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2)
    (τ : PTrans F L) {j : ℕ} (hj : j < ℓ) (a : F) (hbad : ¬ cBadR ℓ w0 zp zs δ τ j a)
    (hnd : cNotDoomed ℓ w0 zp zs v δ (τ.updR j a) (j + 1)) :
    FibDistLE (Wd w0 τ j) (RS (lv L j) (2 * Nd m ℓ (j + 1)) : Set _) δ ∧
      RestrT zp v τ j ∧ 1 - δ ≤ cdens w0 τ j (cdecAt ℓ δ m j (Wd w0 τ j)) ∧
      vvT v τ j = csigmaJ ℓ zp zs j (cdecAt ℓ δ m j (Wd w0 τ j)) := by
  obtain ⟨hRT, c', hc', hdens, hv⟩ := hnd
  simp only [cBadR, not_or, not_and, not_not] at hbad
  obtain ⟨hgood, hres⟩ := hbad
  have hgood' : cGoodAt ℓ δ m j (Wd w0 (τ.updR j a) j) ((τ.updR j a).r j) := by
    rw [Wd_updR]; simpa [PTrans.updR] using hgood
  obtain ⟨hF, hfold, hsub⟩ := crbr_step hL hδ (τ.updR j a) hj hgood' c' hc' hdens
  rw [Wd_updR] at hF hfold hsub
  simp only [PTrans.updR, Function.update_self] at hfold
  set cs := cdecAt ℓ δ m j (Wd w0 τ j)
  have hcs : cs ∈ RS (lv L j) (2 * Nd m ℓ (j + 1)) := (dec_spec hF).1
  -- `s_{j+1}(a) = s^c(a)`, hence `s_{j+1} = s^c`
  have hsa : (τ.s j).eval a = (csRw ℓ w0 zp zs δ τ j).eval a := by
    rw [csRw_eval hL τ hj hcs a, hfold, ← hv]
    simp [vvT, PTrans.updR]
  have hs : τ.s j = csRw ℓ w0 zp zs δ τ j := by
    by_contra hne; exact hres hF hne hsa
  -- the restriction check of index `j+1`
  have hck := hRT j (by omega)
  rw [vvT_updR τ j a j le_rfl, show (τ.updR j a).s = τ.s from rfl, hs, csRw_zp τ hj] at hck
  refine ⟨hF, fun i hi => ?_, ?_, hck.symm⟩
  · have := hRT i (by omega)
    rwa [vvT_updR τ j a i hi.le] at this
  · have hsub' : cWset w0 (τ.updR j a) (j + 1) c' ⊆ cWset w0 τ j cs := by
      rw [cWset_updR] at hsub; exact hsub
    have hle : (cWset w0 (τ.updR j a) (j + 1) c').ncard ≤ (cWset w0 τ j cs).ncard := by
      haveI := hL.finite
      exact Set.ncard_le_ncard hsub' (Set.toFinite _)
    refine hdens.trans ?_
    rw [cdens, cdens]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hle) (Nat.cast_nonneg _)

/-- **Theorem 6.20, item 1 (round 1).** If the output of `cExt` is not a witness for
`(w₀; z, v)`, then for every round-1 message `s_1 ∈ F[X]_{<2}`, `τ_1` is not doomed with
probability at most `(M_1 + 1)/|F|` over `θ_1`. -/
theorem crbr_round_one [Fintype F] [DecidableEq F] {R : ℕ} (hL : IsSmoothDomain L (m + ℓ + R))
    (hℓ : 1 ≤ ℓ) (hδ0 : 0 < δ) (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2)
    (hnw : ¬ cIsWitness ℓ w0 zp zs v δ (cExt ℓ w0 δ)) (τ : PTrans F L)
    (hdeg : (τ.s 0).natDegree ≤ 1) :
    prob (fun a : F => cNotDoomed ℓ w0 zp zs v δ (τ.updR 0 a) 1) ≤
      ((Nat.card (lv L 1) : ℚ) + 1) / Fintype.card F := by
  classical
  have hsub : ∀ a, cNotDoomed ℓ w0 zp zs v δ (τ.updR 0 a) 1 → cBadR ℓ w0 zp zs δ τ 0 a := by
    intro a hnd
    by_contra hbad
    obtain ⟨hF, -, -, hv⟩ := crbr_escape hL hδ τ (by omega) a hbad hnd
    have e0 : 2 * Nd m ℓ (0 + 1) = 2 ^ (m + ℓ) := by rw [Nd_succ (by omega)]; rfl
    have hF0 : FibDistLE w0 (RS L (2 ^ (m + ℓ)) : Set (L → F)) δ := by
      have := hF; rw [e0] at this; exact this
    apply hnw
    refine cExt_witness_of ℓ w0 zp zs v δ hL hF0 ?_
    -- `v = v_0 = σ_0(c) = P_{f*}(z)`
    have hv' : v = csigmaJ ℓ zp zs 0 (cdecAt ℓ δ m 0 w0) := hv
    rw [hv', csigmaJ]
    simp only [cdecAt, cdecTable]
    rw [e0]
    refine cpoly_ccoeffs_congr _ rfl _ _ (fun i => ?_)
    rw [catPt_eq_zfull]
    simp
  calc prob (fun a : F => cNotDoomed ℓ w0 zp zs v δ (τ.updR 0 a) 1)
      ≤ prob (fun a : F => cBadR ℓ w0 zp zs δ τ 0 a) := prob_mono hsub
    _ ≤ _ := by
        rw [prob_def, card_filter_eq_ncard]
        exact div_le_div_of_nonneg_right (card_cBadR hL hδ0 hδ τ (by omega) hdeg)
          (Nat.cast_nonneg _)

/-- **Theorem 6.20, item 2 (round `j+1`, `1 ≤ j < ℓ`).** If `τ_j` is doomed, then for every
round-`(j+1)` message `(s_{j+1}, w_j)` (with `s_{j+1} ∈ F[X]_{<2}`), `τ_{j+1}` is not doomed with
probability at most `(M_{j+1} + 1)/|F|` over `θ_{j+1}`. -/
theorem crbr_round [Fintype F] [DecidableEq F] {R : ℕ} (hL : IsSmoothDomain L (m + ℓ + R))
    (hδ0 : 0 < δ) (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2) (τ : PTrans F L) {j : ℕ} (hj1 : 1 ≤ j)
    (hj : j < ℓ) (hdoom : cDoomed ℓ w0 zp zs v δ τ j) (hdeg : (τ.s j).natDegree ≤ 1) :
    prob (fun a : F => cNotDoomed ℓ w0 zp zs v δ (τ.updR j a) (j + 1)) ≤
      ((Nat.card (lv L (j + 1)) : ℚ) + 1) / Fintype.card F := by
  classical
  have hnd : ¬ cNotDoomed ℓ w0 zp zs v δ τ j := by
    rcases hdoom with h | h
    · omega
    · exact h
  have hsub : ∀ a, cNotDoomed ℓ w0 zp zs v δ (τ.updR j a) (j + 1) →
      cBadR ℓ w0 zp zs δ τ j a := by
    intro a hnd'
    by_contra hbad
    obtain ⟨hF, hRT, hdens, hv⟩ := crbr_escape hL hδ τ hj a hbad hnd'
    apply hnd
    have hmem := (dec_spec hF).1
    change cdecAt ℓ δ m j (Wd w0 τ j) ∈ (RS (lv L j) (2 * Nd m ℓ (j + 1)) : Set _) at hmem
    generalize cdecAt ℓ δ m j (Wd w0 τ j) = cs at hmem hdens hv
    rw [Nd_succ (by omega)] at hmem
    exact ⟨hRT, cs, hmem, hdens, hv⟩
  calc prob (fun a : F => cNotDoomed ℓ w0 zp zs v δ (τ.updR j a) (j + 1))
      ≤ prob (fun a : F => cBadR ℓ w0 zp zs δ τ j a) := prob_mono hsub
    _ ≤ _ := by
        rw [prob_def, card_filter_eq_ncard]
        exact div_le_div_of_nonneg_right (card_cBadR hL hδ0 hδ τ hj hdeg) (Nat.cast_nonneg _)

/-- **Theorem 6.20, item 3 (round `ℓ+1`).** If `τ_ℓ` is doomed, then for every final message
`g`, the verifier accepts with probability at most `(1-δ)^κ` over the query points. -/
theorem crbr_final [Fintype L] {R : ℕ} (hL : IsSmoothDomain L (m + ℓ + R)) (hℓ : 1 ≤ ℓ)
    (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2) (τ : PTrans F L) (hdoom : cDoomed ℓ w0 zp zs v δ τ ℓ)
    (g : Table F m) (κ : ℕ) :
    prob (fun ξ : Fin κ → L => cFullAccepts ℓ w0 zp zs v τ g ξ) ≤ (1 - δ) ^ κ := by
  classical
  have hR : (0 : ℚ) < 1 / 2 ^ R := by positivity
  have hδ1 : (0 : ℚ) ≤ 1 - δ := by linarith
  have hnd : ¬ cNotDoomed ℓ w0 zp zs v δ τ ℓ := by
    rcases hdoom with h | h
    · omega
    · exact h
  haveI := hL.finite
  haveI : Nonempty L := ⟨1⟩
  haveI := lv_finite (L := L) ℓ
  set Pτ := cproverOf τ g
  set wl := ev (lv L ℓ) (vpoly g)
  -- the words of the verifier are those of `τ`
  have hW : ∀ i < ℓ, Pτ.W ℓ w0 τ.r i = Wd w0 τ i := by
    intro i hi
    cases i with
    | zero => rfl
    | succ k => simp only [SumProver.W, if_neg (show k + 1 ≠ ℓ by omega)]; rfl
  have hWl : Pτ.W ℓ w0 τ.r ℓ = wl := cW_last Pτ w0 hℓ τ.r
  have hvv : ∀ i, Pτ.vv v τ.r i = vvT v τ i := by intro i; cases i <;> rfl
  by_cases hRC : RestrT zp v τ ℓ ∧ Pτ.ClosureOK ℓ zs v τ.r
  · obtain ⟨hRT, hCl⟩ := hRC
    -- `λ[w_ℓ] = g`, so the closure check reads `v_ℓ = σ_ℓ(w_ℓ)`
    have hd : 2 ^ m ≤ Nat.card (lv L ℓ) := by
      rw [← Nd_last (ℓ := ℓ)]; exact Nd_le_card hL (by omega)
    have hpoly : polyOf wl = vpoly g :=
      polyOf_ev (degreeLT_mono' hd (vpoly_mem_degreeLT g))
    have hσ : vvT v τ ℓ = csigmaJ ℓ zp zs ℓ wl := by
      rw [← hvv, hCl, csigmaJ, hpoly,
        cpoly_ccoeffs_congr (vpoly g) (show m + ℓ - ℓ = m by omega)
          (fun i => zfull ℓ zp zs (ℓ + i)) zs (fun i => by rw [← zfull_ge zp zs i]; rfl),
        ccoeffs_vpoly]
      rfl
    have hwl : wl ∈ RS (lv L ℓ) (Nd m ℓ ℓ) := by
      rw [Nd_last]; exact ev_mem_RS (vpoly_mem_degreeLT g)
    have hdens : cdens w0 τ ℓ wl < 1 - δ := by
      by_contra hge
      push_neg at hge
      exact hnd ⟨hRT, wl, hwl, hge, hσ⟩
    -- a query point passes all its checks iff it lies in `𝒲_ℓ(w_ℓ)`
    have hq : ∀ ξ : L, Pτ.QueryOK ℓ w0 τ.r ξ → ξ ∈ cWset w0 τ ℓ wl := by
      intro ξ hξ
      obtain ⟨k, rfl⟩ : ∃ k, ℓ = k + 1 := ⟨ℓ - 1, by omega⟩
      refine ⟨fun i hi => ?_, ?_⟩
      · have := hξ.1 i (by omega)
        simp only [SumProver.Chk] at this
        rw [hW i (by omega), hW (i + 1) (by omega)] at this
        exact this
      · have := hξ.1 k (by omega)
        simp only [SumProver.Chk] at this
        rw [hW k (by omega), hWl] at this
        exact this
    calc prob (fun ξ : Fin κ → L => cFullAccepts ℓ w0 zp zs v τ g ξ)
        ≤ prob (fun ξ : Fin κ → L => ∀ t, ξ t ∈ (Set.toFinite (cWset w0 τ ℓ wl)).toFinset) := by
          apply prob_mono
          intro ξ hacc t
          rw [Set.Finite.mem_toFinset]
          exact hq _ (hacc.2.2 t)
      _ = (((Set.toFinite (cWset w0 τ ℓ wl)).toFinset.card : ℚ) / Fintype.card L) ^ κ :=
          prob_forall_mem κ _
      _ ≤ (1 - δ) ^ κ := by
          apply pow_le_pow_left₀ (by positivity)
          rw [← Set.ncard_eq_toFinset_card, ← Nat.card_eq_fintype_card]
          exact hdens.le
  · -- a restriction check or the closure check fails: the verifier always rejects
    have : ∀ ξ : Fin κ → L, ¬ cFullAccepts ℓ w0 zp zs v τ g ξ := by
      intro ξ hacc
      apply hRC
      refine ⟨fun i hi => ?_, hacc.2.1⟩
      have := hacc.1 i hi
      rwa [hvv] at this
    calc prob (fun ξ : Fin κ → L => cFullAccepts ℓ w0 zp zs v τ g ξ)
        = prob (fun _ : Fin κ → L => False) := by
          congr 1; funext ξ; simp only [this ξ]
      _ = 0 := prob_false
      _ ≤ (1 - δ) ^ κ := pow_nonneg hδ1 κ

end Theorem

/-! ### Proposition 6.22 (round-by-round knowledge soundness for `ℓ = 0`) -/

section L0

variable {L : Subgroup Fˣ} {m : ℕ}

/-- The extractor of Proposition 6.22: the table `f^H` with `Δ(w₀, Enc(f^H)) ≤ δ` if there is
one (unique by Lemma 2.13(3)), and the zero table otherwise. -/
noncomputable def cExtH (w0 : L → F) (δ : ℚ) : Table F m := by
  classical exact if h : ∃ f : Table F m, relDist w0 (cEnc L f) ≤ δ then h.choose else 0

/-- **Proposition 6.22 (round-by-round knowledge soundness for `ℓ = 0`).**  With `dist = Δ`,
the only round is the final one.  For every final message `g`, if the verifier accepts with
probability greater than `(1-δ)^κ` over the query points, then the output `f^H` of the extractor
is a witness: `Δ(w₀, Enc(f^H)) ≤ δ` and `P_{f^H}(z) = v`. -/
theorem crbr_l0 [Fintype L] {R : ℕ} (hL : IsSmoothDomain L (m + R)) {δ : ℚ}
    (hδ : δ ≤ (1 - 1 / 2 ^ R) / 2) (w0 : L → F) (zp : ℕ → F) (zs : Fin m → F) (v : F)
    (τ : PTrans F L) (g : Table F m) (κ : ℕ)
    (hacc : (1 - δ) ^ κ < prob (fun ξ : Fin κ → L => cFullAccepts 0 w0 zp zs v τ g ξ)) :
    relDist w0 (cEnc L (cExtH (m := m) w0 δ)) ≤ δ ∧ cpoly (cExtH (m := m) w0 δ) zs = v := by
  classical
  haveI := hL.finite
  haveI : Nonempty L := ⟨1⟩
  have hR : (0 : ℚ) < 1 / 2 ^ R := by positivity
  have hδ1 : (0 : ℚ) ≤ 1 - δ := by linarith
  let S : Finset L := univ.filter (fun ξ => w0 ξ = (vpoly g).eval (((ξ : L) : Fˣ) : F))
  have hev : ∀ ξ : Fin κ → L, cFullAccepts 0 w0 zp zs v τ g ξ ↔
      v = cpoly g zs ∧ ∀ t, ξ t ∈ S := by
    intro ξ
    rw [cFullAccepts, caccepts_zero]
    simp [S, cproverOf]
  by_cases hv : v = cpoly g zs
  · have hp : prob (fun ξ : Fin κ → L => cFullAccepts 0 w0 zp zs v τ g ξ) =
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
    have hagree : agreeSet w0 (cEnc L g) = (S : Set L) := by
      ext ξ; simp [agreeSet, S, cEnc, ev]
    have hdist : relDist w0 (cEnc L g) < δ := by
      have h := agree_add_hdist w0 (cEnc L g)
      rw [hagree, Set.ncard_coe_finset] at h
      have h' : (S.card : ℚ) + hdist w0 (cEnc L g) = Nat.card L := by exact_mod_cast h
      rw [Nat.card_eq_fintype_card] at h'
      unfold relDist
      rw [Nat.card_eq_fintype_card, div_lt_iff₀ hM]
      rw [lt_div_iff₀ hM] at hSM
      linarith
    have hex : ∃ f : Table F m, relDist w0 (cEnc L f) ≤ δ := ⟨g, hdist.le⟩
    have hE : cExtH (m := m) w0 δ = hex.choose := by simp [cExtH, hex]
    have hspec := hex.choose_spec
    have hrate : rate L (2 ^ m) = 1 / 2 ^ R := rate_lv (ℓ := 0) hL (j := 0) (by omega)
    have hδ' : δ ≤ (1 - rate L (2 ^ m)) / 2 := by rw [hrate]; exact hδ
    have huniq := RS_unique_decoding' δ hδ' w0 (cEnc_mem_RS L hex.choose) (cEnc_mem_RS L g)
      hspec hdist.le
    have hfg : hex.choose = g := cEnc_injective
      (show 2 ^ m ≤ Nat.card L from Nd_le_card (ℓ := 0) hL (j := 0) (by omega)) huniq
    rw [hE, hfg]
    exact ⟨hdist.le, hv.symm⟩
  · have : prob (fun ξ : Fin κ → L => cFullAccepts 0 w0 zp zs v τ g ξ) = 0 := by
      rw [← prob_false (Ω := Fin κ → L)]
      congr 1; funext ξ; rw [hev ξ]; simp [hv]
    rw [this] at hacc
    have := pow_nonneg hδ1 κ
    linarith

end L0

end SumFRI
