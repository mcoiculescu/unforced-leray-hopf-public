import UnforcedLeray.Short.PartI.Sub.L_T02_1_4_6_4_5_2
import UnforcedLeray.Short.PartI.Sub.T02_1_4_6_4_5_2_1
import UnforcedLeray.Short.PartI.Sub.T02_1_4_6_4_5_2_2
import UnforcedLeray.Short.PartI.Sub.T02_1_4_6_4_5_2_3
import UnforcedLeray.Short.PartI.Sub.T02_1_4_6_4_5_2_4

/-!
# Part I, task `PartI:T02/1/4/6/4/5/2`: `AdvectionLipLeaf` from the four analytic leaves

Source of record: `the November 2 reference manuscript`, lines 261-288.

Assembles `AdvectionLipLeaf` from `advLipSupDiff_proof`, `advLipSupW_proof`,
`advLipGradBound_proof` and `advLipGradDiff_proof` via `advectionLipLeaf_of`.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartI

theorem advectionLipLeaf_proof : UnforcedLeray.Short.PartI.AdvectionLipLeaf :=
  advectionLipLeaf_of advLipSupDiff_proof advLipSupW_proof advLipGradBound_proof
    advLipGradDiff_proof

end UnforcedLeray.Short.PartI
