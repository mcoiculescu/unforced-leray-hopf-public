import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_2_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.rawSmoothBdd_Sub.rawJointSmooth

/-!
# `PartIII-b:C/ward/12/3/1/2/5/1/2/1`: `InletFieldRegular`

Source `the November 2 reference manuscript`
lines 1206-1222, 5283-5295.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem inletFieldRegular : InletFieldRegular :=
  inletFieldRegularInf_of rawJointSmooth

end UnforcedLeray.Short.PartIIIb.Concrete
