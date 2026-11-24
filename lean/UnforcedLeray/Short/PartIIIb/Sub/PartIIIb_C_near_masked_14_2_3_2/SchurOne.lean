import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_14_2_3_2_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_14_2_3_2_1.AxisNull
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_14_2_3_2_1.KerA
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_14_2_3_2_1.KerB

/-!
# `SchurOne` (`PartIII-b:C/near/masked/14/2/3/2/1`; source 3996-4011)

The Schur bound `SchurOne` follows from the null axis and the two weighted kernel bounds
`SchurKerA`, `SchurKerB`, via `schurOne_of`. Source:
`the November 2 reference manuscript` 3996-4011.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

/-- `SchurOne` from the null axis and the two Schur kernel bounds. -/
theorem schurOne : UnforcedLeray.Short.PartIIIb.NearInst.Masked.SchurOne :=
  schurOne_of axisNull schurKerA schurKerB

end UnforcedLeray.Short.PartIIIb.NearInst.Masked

end
