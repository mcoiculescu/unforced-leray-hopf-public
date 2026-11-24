import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.rawSmoothBdd_Sub.rawJointSmooth

/-!


Source `the November 2 reference manuscript`
lines 2563-2569, 1206-1222.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Measurability of the inlet source gradient `inletFn` in the background regime. -/
theorem inletFnMeas : InletFnMeas :=
  inletFnMeas_of rawJointSmooth

end UnforcedLeray.Short.PartIIIb.Concrete
