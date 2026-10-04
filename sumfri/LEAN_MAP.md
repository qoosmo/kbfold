# Sum-FRI: paper ↔ Lean correspondence

Numbers refer to the compiled paper (`sumfri/paper`, `make` builds `sumfri.pdf`); Lean modules are in
[`lean/SumFRI/`](../lean/SumFRI/), a second library of the KBFold Lean project (Lean `4.23.0`,
Mathlib `v4.23.0`), about 3,400 lines in 9 modules. **No `sorry`.** The only axiom is KBFold's
`bciks_unique` (correlated agreement, Theorem 2.17).

```bash
cd lean
lake build SumFRI
lake env lean SumFRI/Audit.lean   # #print axioms for the main theorems
```

| Paper items | Lean module | Main declarations |
|---|---|---|
| Definition 3.9, eq. (2), Definition 4.1, Lemma 4.2, Definition 4.3, Lemma 4.4, Theorem 4.6 | `Monomial` | `cpoly`, `vpoly`, `vpoly_eval`, `vpoly_eval_one`, `cres`, `cpoly_cres`, `cpoly_cresSeq`, `cfold_vpoly`, `cfoldSeq_vpoly_full`, `cpoly_one` |
| Lemma 4.8(4), Definition 4.10, Lemma 4.11 | `Monomial` | `cwfold_ev`, `rnd0`, `rnd1`, `hround_eq`, `hround_one`, `affine_agree` |
| Definition 5.1, Corollary 4.9, Lemma 5.7, Theorem 5.8 | `Scheme` | `cEnc`, `cfoldUp_Enc`, `hS`, `hS_eval`, `hS_zp`, `SumProver`, `completeness`, `completeness_sum` |
| Lemma 5.2, Definition 6.4, Lemma 4.8(1), Lemmas 6.6, 6.7, Definition 6.8, Lemmas 6.9, 6.10 | `Fibre` | `vpoly_ccoeffs`, `cEnc_injective`, `cdecTable`, `cwfold_congr`, `cfar_fold`, `csurvive`, `CGood`, `ncard_not_cgood_le`, `cone_step` |
| Lemmas 6.11, 6.12, Theorem 6.13, Corollaries 6.14, 6.15, Proposition 6.16 | `Soundness` | `cPass_card`, `cchain`, `cchain_final`, `csoundness_far`, `csoundness_close`, `ceval_binding`, `soundness_sum`, `sum_binding`, `cno_folding` |
| Definition 6.17, Lemmas 6.18, 6.19, Theorem 6.20 (items 1–3), Proposition 6.22 | `RBR` | `cNotDoomed`, `cExt`, `crbr_step`, `ccoeffs_cwfold`, `csRw_zp`, `csRw_eval`, `crbr_round_one`, `crbr_round`, `crbr_final`, `crbr_l0` |
| Theorem 6.20 ("Consequently"), Remark 6.21 | `RBRGeneric` | `crbr_knowledge`, `crbr_binding` |
| Definition 6.24, Lemma 6.25, Theorem 6.26, Lemma 6.28 (core) | `NonInteractive` | `cKState`, `crbr_stepE`, `crbr_erasures_one`, `crbr_erasures_round`, `crbr_erasures_final`, `crrbr_round`, `crrbr_final`, `ccr_unique_core` |
| Lemma 5.6, Theorem 6.32 item 1 | `Skip` | `SumProver.augW`, `caccepts_aug`, `csoundness_far_J`, `csoundness_close_J`, `ceval_binding_J`, `soundness_sum_J` |

**Reused from KBFold** (`lean/KBFold/`): probability lemmas (Lemmas 3.2–3.4), the generic
round-by-round framework (Definition 3.7, Lemmas 3.8, 3.12), smooth domains and Reed–Solomon
codes (Lemmas 2.9, 2.12, 2.13, 2.16), fibre distance and decoding (Definition 6.1, Lemmas 6.2,
6.3), sampling and fibre strings (Lemma 6.23, §6.7).

**`#print axioms`** (`lean/SumFRI/Audit.lean`):

- Lean's standard three only (`propext`, `Classical.choice`, `Quot.sound`): `cfoldSeq_vpoly_full`,
  `vpoly_eval_one`, `completeness`, `completeness_sum`, `cno_folding`, `crbr_l0`, `crrbr_final`,
  `ccr_unique_core`;
- additionally `KBFold.bciks_unique`: `cfar_fold`, `csoundness_far`, `csoundness_close`,
  `ceval_binding`, `soundness_sum`, `sum_binding`, `crbr_knowledge`, `crbr_binding`,
  `crrbr_round`, `csoundness_close_J`, `soundness_sum_J`.

**Not formalised.** Theorem 3.14 and Corollary 6.27 (quantum random oracle model, quoted from
CDHZ25); Merkle-tree statements and the collision step of Lemma 6.28; Fact 2.14 and Lemma 2.15;
running times and operation counts; Lemma 5.5 and items 2–4 of Theorem 6.32; Sections 7–8.
