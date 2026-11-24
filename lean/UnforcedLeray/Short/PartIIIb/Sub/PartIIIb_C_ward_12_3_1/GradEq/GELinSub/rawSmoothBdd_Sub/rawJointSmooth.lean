import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.rawSmoothBdd_Sub.Sub.Core
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.rawSmoothBdd_Sub.Sub.RingLiftSmoothReal

/-!


Source `the November 2 reference manuscript`
lines 1214, 1305-1325.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Joint `C^∞` smoothness of `(τ,y) ↦ raw τ y` on `ℝ × ℝ³` in the background regime. -/
theorem rawJointSmooth : RawJointSmooth :=
  rawJointSmooth_of ringLiftSmoothReal

end UnforcedLeray.Short.PartIIIb.Concrete
