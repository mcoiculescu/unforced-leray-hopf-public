import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_org_2_3_3_4
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_org_2_3_3_5
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_org_2_3_3_6

/-!
# `PartII-b:T10/org/2/3/3` (`LerayCDensity`): unconditional assembly

Applies `lerayCDensity_of` to the three unconditional inputs `curlPotentialC_proof`
(`PartII-b_T10_org_2_3_3_4`), `cutoffCurlSolTest_proof` (`PartII-b_T10_org_2_3_3_5`) and
`cutoffCurlConverge_proof` (`PartII-b_T10_org_2_3_3_6`).
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.IIb

theorem lerayCDensity_proof : UnforcedLeray.Short.IIb.LerayCDensity :=
  lerayCDensity_of curlPotentialC_proof cutoffCurlSolTest_proof cutoffCurlConverge_proof

end UnforcedLeray.Short.IIb
