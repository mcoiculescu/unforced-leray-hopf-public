import UnforcedLeray.Short.PartIIIb.Sub.Tasks.ra_9_1_2_9_2_1.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.HpPsiTermSummable.Gauss

/-!
# `psiSummandExpand` (task `PartIII-b:C/asrc/ra/9/1/2/9/2/1/3`)
Source `the November 2 reference manuscript` lines 5063-5071, 5076-5079, 4979.
The scalar summand `psiSummandM` is linear in the entries of `A^y`: `merTrace` and `merApply`
expand over the meridional basis `mi`, and `fderiv` of `psij` is given by `gp_fderiv_psij`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

theorem psiSummandExpand : PsiSummandExpand := by
  intro ν _hν χf A j p _hp
  simp (config := {decide := true}) only [psiSummandM, psiSummandGauss, gp_fderiv_psij, psij, merTrace,
    merApply, Ay, mi, comp2, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul, Fin.isValue,
    ite_true, ite_false, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

end UnforcedLeray.Short.PartIIIb.Concrete
