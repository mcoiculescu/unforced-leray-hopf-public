import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1_org2_smooth_6
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1_org2_smooth_6.Leaf1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1_org2_smooth_6.Leaf2

/-!
# Leaf 6: `ParamIntegralSmooth` from the two joint-continuity leaves (task
`PartIII-b:C/flatset/col/7/1/1/2/1/org2/smooth/6`, target `paramIntegralSmooth`).

`paramIntegralSmooth_of` reduces `ParamIntegralSmooth` to `ProdJointCont` (Leaf 1,
`prodJointCont`) and `ShiftJointCont` (Leaf 2, `shiftJointCont`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem paramIntegralSmooth : ParamIntegralSmooth :=
  paramIntegralSmooth_of prodJointCont shiftJointCont

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
