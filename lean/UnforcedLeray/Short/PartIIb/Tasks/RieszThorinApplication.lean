import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T18
import UnforcedLeray.Short.PartIIb.Tasks.RieszThorinApplication.HrOperatorFamily
import UnforcedLeray.Short.PartIIb.Tasks.RieszThorinApplication.DmLpRealization

/-!
# Part II-b, Task `T18`: Riesz-Thorin application (`LpInterpolationStep`)

Source: `the November 2 reference manuscript` (SP), lines 1992-2005 (`bg:lp-free-comparison`).

Decomposed into `Short/PartII-b/Sub/PartII-b_T18.lean`:
* `PartII-b:T18/1` (`HrComparisonOperatorFamily` in `Tasks/RieszThorinApplication/HrOperatorFamily.lean`);
* `PartII-b:T18/2` (`DmLpRealizationOfHrOperator` in `Tasks/RieszThorinApplication/DmLpRealization.lean`);
* conditional assembly `UnforcedLeray.Short.IIb.lpInterpolationStep_of_leaves`.

Assembled here from the proved leaves `hrComparisonOperatorFamily_proof` and
`dmLpRealizationOfHrOperator_proof`.
-/

set_option autoImplicit false
noncomputable section

namespace UnforcedLeray.Short.IIb

theorem lpInterpolationStep_of (h16 : UnforcedLeray.Short.IIb.HilbertBodyComparison) :
    UnforcedLeray.Short.IIb.LpInterpolationStep :=
  lpInterpolationStep_of_leaves hrComparisonOperatorFamily_proof dmLpRealizationOfHrOperator_proof h16

end UnforcedLeray.Short.IIb

end
