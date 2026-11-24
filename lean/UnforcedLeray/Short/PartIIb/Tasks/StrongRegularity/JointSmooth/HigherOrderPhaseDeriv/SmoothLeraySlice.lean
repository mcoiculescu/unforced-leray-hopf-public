import UnforcedLeray.Short.PartIIb.Sub.PartIIb_S3_1_2_1
import UnforcedLeray.Short.PartIIb.Tasks.StrongRegularity.JointSmooth.HigherOrderPhaseDeriv.SmoothLeraySlice.RepExists
import UnforcedLeray.Short.PartIIb.Tasks.StrongRegularity.JointSmooth.HigherOrderPhaseDeriv.SmoothLeraySlice.DerivZero

/-!
# `PartII-b:S3/1/2/1`: Smooth `L⁴(ℝ³)` Leray slice regularity (`SmoothLeraySlice.lean`, SP 2552, 2559-2562)

Decomposed via `UnforcedLeray.Short.«PartII-b».Sub.«PartII-b_S3_1_2_1»`: once `PartII-b:S3/1/2/1/1`
(`smoothLerayRepExists_proof : SmoothLerayRepExists` in
`UnforcedLeray.Short.«PartII-b».Tasks.StrongRegularity.JointSmooth.HigherOrderPhaseDeriv.SmoothLeraySlice.RepExists`)
and `PartII-b:S3/1/2/1/2` (`smoothLeraySliceDerivZero_proof : SmoothLeraySliceDerivZero` in
`UnforcedLeray.Short.«PartII-b».Tasks.StrongRegularity.JointSmooth.HigherOrderPhaseDeriv.SmoothLeraySlice.DerivZero`)
are proved, assemble `smoothLeraySliceRegularity_proof` via `smoothLeraySliceRegularity_of`.
-/

namespace UnforcedLeray.Short.IIb

theorem smoothLeraySliceRegularity_proof : UnforcedLeray.Short.IIb.SmoothLeraySliceRegularity :=
  smoothLeraySliceRegularity_of
    smoothLerayRepExists_proof smoothLeraySliceDerivZero_proof

end UnforcedLeray.Short.IIb

