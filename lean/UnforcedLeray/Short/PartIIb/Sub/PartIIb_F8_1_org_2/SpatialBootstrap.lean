import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F8_1_org_2_2
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F8_1_org_2.SpatialBootstrap.WeakMildUnique
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F8_1_org_2.SpatialBootstrap.MildBootstrap

/-!
# Part II-b, task `PartII-b:F8/1/org/2/2` — Assembly of `RealCylOseenSpatialBootstrap`
(SP 2052–2053, 2213–2217, 2296–2301)

Assembles `RealCylOseenSpatialBootstrap` from `realCylOseenSpatialBootstrap_of_leaves`
and the two leaves `realCylOseenWeakMildUnique_proof` and
`realCylOseenMildSpatialBootstrap_proof`.
-/

namespace UnforcedLeray.Short.IIb

theorem realCylOseenSpatialBootstrap_proof : UnforcedLeray.Short.IIb.RealCylOseenSpatialBootstrap :=
  realCylOseenSpatialBootstrap_of_leaves
    realCylOseenWeakMildUnique_proof
    realCylOseenMildSpatialBootstrap_proof

end UnforcedLeray.Short.IIb
