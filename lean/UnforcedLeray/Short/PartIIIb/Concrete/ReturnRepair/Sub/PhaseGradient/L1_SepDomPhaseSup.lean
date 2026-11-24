import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.Defs
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_1_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_1_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_1_3

/-!
# `PartIII-b:C/rep/2/1` (task L1): `SepDomPhaseSup` from the three analytic facts

Source `the November 2 reference manuscript` 3624-3647 (`sep:young`) and
3838-3845, 5219-5221 (normalised phase estimate over `P ≤ 1`).  The three analytic Props
`SepDomMinkowski`, `SepKdYoungScaled`, `PeriodicDilationSum` are proved in the sibling files
`Sub.PartIII-b_C_rep_2_1_1`, `_2`, `_3`; the assembly `sepDomPhaseSup_of` is proved in
`Sub.PartIII-b_C_rep_2_1`.  This file composes them.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **(S1a) Separated domination in phase supremum** (source 3624-3647, 5219-5221), with the three
analytic inputs discharged: Minkowski in `λ`, scaled Young in `y`, and the periodic dilation sum. -/
theorem sepDomPhaseSup : SepDomPhaseSup :=
  sepDomPhaseSup_of sepDomMinkowski_proved sepKdYoungScaled_proved periodicDilationSum_proved

end UnforcedLeray.Short.PartIIIb.Concrete

end
