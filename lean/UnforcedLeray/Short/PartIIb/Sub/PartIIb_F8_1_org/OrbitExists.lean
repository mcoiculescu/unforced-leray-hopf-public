import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F8_1_org_2
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F8_1_org_2.WeakH1Exists
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F8_1_org_2.SpatialBootstrap
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F8_1_org_2.JointSmoothUpgrade

/-!
# Part II-b, task `PartII-b:F8/1/org/2` — Assembly of `CylOseenOrbitExists` (SP 2213–2217, 2296–2301)

Assembles `CylOseenOrbitExists` from `cylOseenOrbitExists_of_leaves` and the three
leaf proofs `realCylOseenWeakH1Exists_proof`, `realCylOseenSpatialBootstrap_proof`,
and `realCylOseenJointSmoothUpgrade_proof`.
-/

namespace UnforcedLeray.Short.IIb

theorem cylOseenOrbitExists_proof : UnforcedLeray.Short.IIb.CylOseenOrbitExists :=
  cylOseenOrbitExists_of_leaves
    realCylOseenWeakH1Exists_proof
    realCylOseenSpatialBootstrap_proof
    realCylOseenJointSmoothUpgrade_proof

end UnforcedLeray.Short.IIb
