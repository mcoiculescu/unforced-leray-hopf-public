import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_1_org3_b_L3.Assembly
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_1_org3_b_L3.EigenLeaf
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_1_org3_b_L3.RelBoundLeaf

/-!
# Leaf B3: `PlanarDampedDysonBound`

Source: `the November 2 reference manuscript` (SP), lines 2926-2935, 2976-2980.

Assembles `PlanarB.planarDampedDysonBound_proof` from `PlanarDysonL3.planarDampedDysonBound_of`,
`PlanarDysonL3.planarEigenLeaf_proof`, and `PlanarDysonL3.planarRelBoundLeaf_proof`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIIa.BlockPropagatorInteriorSub.OrgSplit3.PlanarB

theorem planarDampedDysonBound_proof
    (κ : UnforcedLeray.Short.IIIa.PlanarFrameKernels) :
    PlanarDampedDysonBound κ :=
  UnforcedLeray.Short.IIIa.PlanarDysonL3.planarDampedDysonBound_of κ
    (UnforcedLeray.Short.IIIa.PlanarDysonL3.planarEigenLeaf_proof κ)
    (UnforcedLeray.Short.IIIa.PlanarDysonL3.planarRelBoundLeaf_proof κ)

end UnforcedLeray.Short.IIIa.BlockPropagatorInteriorSub.OrgSplit3.PlanarB
