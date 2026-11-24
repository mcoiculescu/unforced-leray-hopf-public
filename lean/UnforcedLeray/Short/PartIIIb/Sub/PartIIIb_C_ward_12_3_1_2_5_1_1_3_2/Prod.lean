import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_2_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_2_2.DerivBound
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.rawSmoothBdd_Sub.rawJointSmooth

/-!


Source `the November 2 reference manuscript`
lines 2545-2551, 2563-2569, 1206-1222, 1217-1219.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem inletFnNearOfJets : InletFnNearOfJets :=
  inletFnNearOfJets_of rawJointSmooth inletSrcDerivBound

end UnforcedLeray.Short.PartIIIb.Concrete
