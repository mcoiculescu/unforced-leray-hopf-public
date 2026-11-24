import UnforcedLeray.Short.PartI.Sub.PartI_T09_5_org_1_org_c.SumLimsup
import UnforcedLeray.Short.PartI.Sub.PartI_T09_5_org_1_org_c.SumLimsup.CurlGradCutoff
import UnforcedLeray.Short.PartI.Sub.PartI_T09_5_org_1_org_c.SumLimsup.CutoffErrorLimit

/-!
# `PartI:T09/5/org/1/org/c`: proof of `TrainJetSumLimsup`

Source: `the November 2 reference manuscript`,
lines 270-288.  Proves the target `TrainJetSumLimsup` (`JetSum.lean`) by the conditional theorem
`trainJetSumLimsup_of` (`SumLimsup.lean`), fed with `curlGradIdentity_of` applied to the two leaves
`CurlGradCutoff` (`SumLimsup/CurlGradCutoff.lean`) and `CutoffErrorLimit`
(`SumLimsup/CutoffErrorLimit.lean`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartI

/-- **`TrainJetSumLimsup`** (lines 270-288): the summed jet energy satisfies
`limsup_{s→0+} S_j(s) ≤ S_j(0)` for every BUC train. -/
theorem trainJetSumLimsup_proof : TrainJetSumLimsup :=
  trainJetSumLimsup_of (curlGradIdentity_of curlGradCutoff_proof cutoffErrorLimit_proof)

end UnforcedLeray.Short.PartI
