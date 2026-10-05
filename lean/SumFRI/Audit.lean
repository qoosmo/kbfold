/-
SumFRI/Audit.lean
Prints the axioms used by the main theorems of the Sum-FRI formalisation
(`lake env lean SumFRI/Audit.lean`).  The expected output: the standard axioms `propext`,
`Classical.choice`, `Quot.sound`, and, for the soundness results, the single project axiom
`KBFold.bciks_unique` (correlated agreement, Theorem 2.17).
-/
import SumFRI
open SumFRI
#print axioms SumFRI.cfoldSeq_vpoly_full
#print axioms SumFRI.vpoly_eval_one
#print axioms SumFRI.completeness
#print axioms SumFRI.completeness_sum
#print axioms SumFRI.cfar_fold
#print axioms SumFRI.csoundness_far
#print axioms SumFRI.csoundness_close
#print axioms SumFRI.ceval_binding
#print axioms SumFRI.soundness_sum
#print axioms SumFRI.sum_binding
#print axioms SumFRI.cno_folding
#print axioms SumFRI.crbr_knowledge
#print axioms SumFRI.crbr_binding
#print axioms SumFRI.crbr_l0
#print axioms SumFRI.crrbr_round
#print axioms SumFRI.crrbr_final
#print axioms SumFRI.ccr_unique_core
#print axioms SumFRI.csoundness_close_J
#print axioms SumFRI.soundness_sum_J
#print axioms SumFRI.cwfold_sqPt
#print axioms SumFRI.cfoldUp_local
#print axioms SumFRI.crbr_round_one_J
#print axioms SumFRI.crbr_round_J
#print axioms SumFRI.crbr_final_J
#print axioms SumFRI.crrbr_round_J
#print axioms SumFRI.crrbr_final_J
#print axioms SumFRI.completeness_J
#print axioms SumFRI.completeness_sum_J
#print axioms SumFRI.ceval_binding'_J
#print axioms SumFRI.sum_binding_J
