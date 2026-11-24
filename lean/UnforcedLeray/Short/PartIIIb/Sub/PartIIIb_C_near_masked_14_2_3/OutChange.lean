import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_14_2_3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_14_2_3_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_14_2_3_1.LiftAxisym
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_14_2_3_1.SliceAxisym
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_14_2_3_1.SliceJointMeas
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_14_2_3_1.OutChangeVar
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_14_2_3_1_4

/-!
# Far output change of variables (`PartIII-b:C/near/masked/14/2/3/1` assembly)

Source: `the November 2 reference manuscript`
2683, 3604-3610, 3996-4011.

Assembles `FarOutChange` from the analytic inputs `liftAxisym`, `sliceAxisym`, `sliceJointMeas`
and the exact `-5/2` change of variables `outChangeVarExp`, via `farOutChange_of_exp`.

The unrepaired `OutChangeVar` (exponent `-3/2`) is false (counterexample in
`PartIII-b_C_near_masked_14_2_3_1_4.lean`), so `farOutChange_of` cannot be applied with
`outChangeVar`; the repaired route `farOutChange_of_exp` is used instead.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

/-- Far output change of variables, assembled from the four proved inputs. -/
theorem farOutChange : UnforcedLeray.Short.PartIIIb.NearInst.Masked.FarOutChange :=
  farOutChange_of_exp liftAxisym sliceAxisym sliceJointMeas outChangeVarExp

end UnforcedLeray.Short.PartIIIb.NearInst.Masked
