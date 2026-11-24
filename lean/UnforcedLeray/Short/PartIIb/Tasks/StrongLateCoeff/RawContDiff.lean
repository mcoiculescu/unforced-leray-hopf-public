import UnforcedLeray.Short.PartIIb.Sub.RawRegularityOnce
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.rawSmoothBdd_Sub.rawJointSmooth

/-!


Source `the November 2 reference manuscript`
lines 1214, 1305-1325.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

theorem rawContDiff : UnforcedLeray.Short.IIb.RawContDiff :=
  rawContDiff_of_concreteJoint UnforcedLeray.Short.PartIIIb.Concrete.rawJointSmooth

end UnforcedLeray.Short.IIb
