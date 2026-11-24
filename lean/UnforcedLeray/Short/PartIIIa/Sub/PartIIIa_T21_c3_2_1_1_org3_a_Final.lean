import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_1_org3_a_D
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_1_org3_a_D1

/-!
# Part III-a, `PartIII-a:T21/c3/2/1/1/org/3/a/1`: leaf D assembled

Source: `the November 2 reference manuscript` (SP) 2962-2964.

Composes `RelFreeTestSub.relFreeTestLimit_of` (leaf file `_D`) with the proved free transport
limit `RelFreeTestSub.freeMovingTransportLimit` (leaf file `_D1`). This file is separate from
`_D` to avoid an import cycle.
-/

namespace UnforcedLeray.Short.IIIa

/-- Leaf D: the relative free-test limit for `planarRelTransportRe` (SP 2962-2964). -/
theorem relFreeTestLimit (κ : PlanarFrameKernels) :
    UnforcedLeray.Short.IIIa.BlockPropagatorInteriorSub.OrgSplit3.StrongA.RelFreeTestLimitTo κ
      UnforcedLeray.Short.IIIa.BlockPropagatorInteriorSub.OrgSplit3.StrongA.planarRelTransportRe :=
  RelFreeTestSub.relFreeTestLimit_of RelFreeTestSub.freeMovingTransportLimit κ

end UnforcedLeray.Short.IIIa
