# Paper ↔ Lean correspondence

Numbers refer to the compiled paper [`paper/kbfold.pdf`](../paper/kbfold.pdf); Lean modules are in [`lean/KBFold/`](../lean/KBFold/).

| Paper items | Lean module | Main declarations |
|---|---|---|
| Lemma 2.5, Proposition 2.6, Corollary 2.7, Definition 2.10, Lemma 2.11, Lemma 2.12 | `Multilinear` | `eqv_pt`, `mle_pt`, `mle_eqTable`, `mle_res`, `map_mle` |
| Lemma 2.9 | `Mobius` | `mle_eq_sum_mono`, `table_coeff_form` |
| Definition 2.14, Lemma 2.15, Definition 2.16, Definition 2.17, Lemma 2.18, Lemma 2.19, Lemma 2.22 | `Domain` | `IsSmoothDomain`, `card_powDom_and_ker`, `fibre`, `RS`, `RS_agree_lt`, `RS_unique_decoding`, `evenW`, `oddW` |
| Theorem 2.23 | `BCIKS` | axiom `bciks_unique` |
| Lemma 3.2, Lemma 3.3, Lemma 3.4 | `Probability` | `sequential_challenges`, `independent_queries`, `randomised_prover_le` |
| Definition 3.5, Definition 3.6, Definition 3.7, Lemma 3.8, Lemma 3.9, Lemma 3.12 | `RoundByRound` | `RBRSound`, `RBRKnowledge`, `rbr_knowledge_overall`, `sumcheck_sound_iop`, `rbr_knowledge_binding` |
| Definition 4.1, Theorem 4.8, Definition 4.10 | `Kernel` | `kernel`, `ofCoords`, `ofCoordsLin_bijective`, `exists_unique_coords` |
| §4.2, §4.4, §4.5 | `LowDegree`, `Mobius` | `coeff_kernel`, `kron_mul`, `Kmat_inv`, `coeff_ofCoords`, `lowDegree_iff`, `RS_eq_charCond`, `eval_ofCoords` |
| Proposition 5.1, Definition 5.2, Theorem 5.3, Corollary 5.4 | `Kernel`, `WordFold` | `pfold`, `fold_dictionary`, `pfoldList_ofCoords`, `pfoldSeq_ofCoords` |
| Definition 5.5, Lemma 5.6, Lemma 5.7, Proposition 5.8, Corollary 5.9, Definition 5.10, Proposition 5.11 | `WordFold` | `wfold`, `wfold_line`, `wfold_ev`, `codeword_fold`, `cfold_eq_pfold` |
| Lemma 6.2, Lemma 6.4, Theorem 6.5 | `Fibre`, `Protocol`, `Completeness` | `Enc_injective`, `honest_table`, `honS_eval`, `completeness` |
| Definition 7.1, Lemma 7.2, Lemma 7.3, Definition 7.4, Lemma 7.6, Lemma 7.7, Definition 7.8, Lemma 7.9, Lemma 7.10 | `Fibre` | `fibDist`, `fib_unique`, `dec`, `decTable`, `far_fold`, `survive`, `Good`, `ncard_not_good_le`, `one_step` |
| Lemma 7.11, Lemma 7.12, Theorem 7.13, Corollary 7.14, Proposition 7.15 | `Soundness` | `Pass_card`, `chain`, `chain_final`, `soundness_far`, `soundness_close`, `eval_binding`, `no_folding` |
| Definition 7.16, Lemma 7.17, Lemma 7.18, Theorem 7.19, Proposition 7.21 | `RBR`, `RBRGeneric` | `Doomed`, `rbr_step`, `sCw_eval`, `rbr_round_one`, `rbr_round`, `rbr_final`, `rbr_knowledge`, `rbr_l0` |
| Lemma 7.22, Definition 7.23, Lemma 7.24, Theorem 7.25, Lemma 7.27 | `NonInteractive` | `prob_sample_le`, `KState`, `rbr_stepE`, `rbr_erasures_one`, `rrbr_round`, `rrbr_final`, `cr_unique_core` |

**Axiom.** `bciks_unique` (`BCIKS.lean`) = Theorem 2.23. `#print axioms` (see `lean/KBFold/Audit.lean`):

- no axiom beyond Lean's standard three (`propext`, `Classical.choice`, `Quot.sound`): `fold_dictionary`, `ofCoordsLin_bijective`, `lowDegree_iff`, `eval_ofCoords`, `codeword_fold`, `completeness`, `rrbr_final`, `cr_unique_core`, `sumcheck_sound_iop`;
- additionally `bciks_unique`: `soundness_far`, `soundness_close`, `eval_binding`, `rbr_knowledge`, `rrbr_round`.

**Not formalised.** Theorem 3.16 and Corollary 7.26 (quantum random oracle model, quoted from CDHZ25); Merkle-tree lemmas and the collision step of Lemma 7.27; Facts 2.2 and 2.20; Lemma 2.21; Remark 4.9; running times and operation counts; §8–§9.
