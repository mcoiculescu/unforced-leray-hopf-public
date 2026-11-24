import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_2.Jets
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_2.Prod
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.rawSmoothBdd_Sub.rawDerivBdd

/-!
# `inletFnNearBound` (assembly of near-axis bound for the inlet source)

Source `the November 2 reference manuscript`
lines 2545-2551, 2563-2569, 1206-1222.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem inletFnNearBound : InletFnNearBound :=
  inletFnNearBound_of inletENearJets inletFnNearOfJets rawDerivBdd

end UnforcedLeray.Short.PartIIIb.Concrete
