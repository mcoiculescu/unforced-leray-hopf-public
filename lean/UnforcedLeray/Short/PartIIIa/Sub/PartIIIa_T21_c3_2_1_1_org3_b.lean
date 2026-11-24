import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_1_org3_b0
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_1_org3_b_L1
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_1_org3_b_L2
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_1_org3_b_L3
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_1_org3_b_L4

/-! Parent file of `PartIII-a:T21/c3/2/1/1/org/3/b`; the conditional assembly and the four leaf
`Prop`s are in `..._org3_b0.lean` (`PlanarB.relPlanarInteraction_of`). The final theorem
`relPlanarInteraction` is proved here from the four leaves. -/

set_option autoImplicit false

namespace UnforcedLeray.Short.IIIa.BlockPropagatorInteriorSub.OrgSplit3

theorem relPlanarInteraction (κ : PlanarFrameKernels) :
    UnforcedLeray.Short.IIIa.BlockPropagatorInteriorSub.OrgSplit3.RelPlanarInteraction κ :=
  PlanarB.relPlanarInteraction_of κ
    (PlanarB.planarDampedIntExists_proof κ)
    (PlanarB.planarDampedIntCompact_proof κ)
    (PlanarB.planarDampedDysonBound_proof κ)
    (PlanarB.planarDampedIntLimit_proof κ)

end UnforcedLeray.Short.IIIa.BlockPropagatorInteriorSub.OrgSplit3
