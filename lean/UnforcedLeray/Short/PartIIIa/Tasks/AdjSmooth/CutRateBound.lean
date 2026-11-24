import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_3_2
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.CutRatePointwise
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.CutRateIntegrable
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.CutWeightX2

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIIa

/-- `CutRateBound` from its three proved leaves. -/
theorem cutRateBound : UnforcedLeray.Short.IIIa.CutRateBound :=
  UnforcedLeray.Short.IIIa.cutRateBound_of cutRatePointwise cutRateIntegrable cutWeightX2

end UnforcedLeray.Short.IIIa
