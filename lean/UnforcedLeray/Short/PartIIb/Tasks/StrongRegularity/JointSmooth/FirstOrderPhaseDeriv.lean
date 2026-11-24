import UnforcedLeray.Short.PartIIb.Sub.PartIIb_S3_1_1
import UnforcedLeray.Short.PartIIb.Tasks.StrongRegularity.JointSmooth.FirstOrderPhaseDeriv.MorreyL4
import UnforcedLeray.Short.PartIIb.Tasks.StrongRegularity.JointSmooth.FirstOrderPhaseDeriv.PhaseDerivStep

/-!
# `PartII-b:S3/1/1` first-order phase derivative (`FirstOrderPhaseDeriv.lean`, SP 2519-2523, 2559-2562)

Decomposed via `UnforcedLeray.Short.«PartII-b».Sub.«PartII-b_S3_1_1»`: once `PartII-b:S3/1/1/1`
(`smoothMorreyL4FieldBound_proof : SmoothMorreyL4FieldBound` in
`UnforcedLeray.Short.«PartII-b».Tasks.StrongRegularity.JointSmooth.FirstOrderPhaseDeriv.MorreyL4`)
and `PartII-b:S3/1/1/2` (`bgFirstPhaseDerivStep_proof : BgFirstPhaseDerivStep` in
`UnforcedLeray.Short.«PartII-b».Tasks.StrongRegularity.JointSmooth.FirstOrderPhaseDeriv.PhaseDerivStep`)
are proved, assemble:
```lean
theorem bgFirstOrderPhaseDeriv_proof :
    UnforcedLeray.Short.IIb.BgFirstOrderPhaseDeriv :=
  bgFirstOrderPhaseDeriv_of
    smoothMorreyL4FieldBound_proof bgFirstPhaseDerivStep_proof
```
-/

theorem UnforcedLeray.Short.IIb.bgFirstOrderPhaseDeriv_proof :
    UnforcedLeray.Short.IIb.BgFirstOrderPhaseDeriv :=
  UnforcedLeray.Short.IIb.bgFirstOrderPhaseDeriv_of
    UnforcedLeray.Short.IIb.smoothMorreyL4FieldBound_proof
    bgFirstPhaseDerivStep_proof
