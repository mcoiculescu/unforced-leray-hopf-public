import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F8_1_org_3
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F8_1_org.DuhamelRegularity.UnitDuhamelStep
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F8_1_org.DuhamelRegularity.UnitWeakUnique

/-!
# Part II-b, task `PartII-b:F8/1/org/3` — Assembly of `MeridionalDuhamelRegularity` (SP 2301–2305)

Assembles `MeridionalDuhamelRegularity` from `meridionalDuhamelRegularity_of_leaves`
and the two leaf proofs `cylUnitDuhamelStep_proof` and `cylUnitWeakHomogeneousUnique_proof`.
-/

namespace UnforcedLeray.Short.IIb

theorem meridionalDuhamelRegularity_proof : UnforcedLeray.Short.IIb.MeridionalDuhamelRegularity :=
  meridionalDuhamelRegularity_of_leaves
    cylUnitDuhamelStep_proof
    cylUnitWeakHomogeneousUnique_proof

end UnforcedLeray.Short.IIb
