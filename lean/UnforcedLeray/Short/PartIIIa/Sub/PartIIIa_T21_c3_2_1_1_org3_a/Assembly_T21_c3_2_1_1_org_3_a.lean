import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_1_org3_a_Final
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_1_org3_a_N

/-!
# Part III-a, `PartIII-a:T21/c3/2/1/1/org/3/a`: assembly of the strong limit (SP 2962-2972)

Composes the two leaves `relFreeTestLimit` (file `_Final`, leaf D) and `relFreeNormLimit`
(file `_N`, leaf N) with `OrgSplit3.StrongA.relStrongLimit_of` (file `_a`).
-/

namespace UnforcedLeray.Short.IIIa

theorem relStrongLimit (κ : PlanarFrameKernels) :
    UnforcedLeray.Short.IIIa.BlockPropagatorInteriorSub.OrgSplit3.RelStrongLimit κ :=
  UnforcedLeray.Short.IIIa.BlockPropagatorInteriorSub.OrgSplit3.StrongA.relStrongLimit_of κ
    (relFreeTestLimit κ) (relFreeNormLimit κ)

end UnforcedLeray.Short.IIIa
