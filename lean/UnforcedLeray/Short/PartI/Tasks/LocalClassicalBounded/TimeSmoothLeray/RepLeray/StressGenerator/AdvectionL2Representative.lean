import UnforcedLeray.Short.PartI.Sub.T02_1_4_6_4_5
import UnforcedLeray.Short.PartI.Sub.T02_1_4_6_4_5_1
import UnforcedLeray.Short.PartI.Sub.T02_1_4_6_4_5_2

/-!
# Part I, task `PartI:T02/1/4/6/4/5`: the unconditional advection representative

Source of record: `the November 2 reference manuscript`, lines 261-288.

Assembles `AdvectionL2Representative` from the membership leaf `advectionMemLpLeaf_proof`
(`Sub/T02_1_4_6_4_5_1.lean`) and the Lipschitz leaf `advectionLipLeaf_proof`
(`Sub/T02_1_4_6_4_5_2.lean`) via `advectionL2Representative_of`.
-/

namespace UnforcedLeray.Short.PartI

theorem advectionL2Representative : AdvectionL2Representative :=
  advectionL2Representative_of advectionMemLpLeaf_proof advectionLipLeaf_proof

end UnforcedLeray.Short.PartI
