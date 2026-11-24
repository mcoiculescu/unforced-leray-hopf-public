import UnforcedLeray.Short.PartIIb.Sub.RawRegularityOnce
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.rawSmoothBdd_Sub.rawJointSmooth

namespace UnforcedLeray.Short.IIb

theorem rawJointSmooth : UnforcedLeray.Short.IIb.RawJointSmooth :=
  rawJointSmooth_of_concreteJoint UnforcedLeray.Short.PartIIIb.Concrete.rawJointSmooth

end UnforcedLeray.Short.IIb
