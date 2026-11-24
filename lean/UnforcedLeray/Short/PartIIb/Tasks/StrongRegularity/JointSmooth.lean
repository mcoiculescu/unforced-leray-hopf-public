import UnforcedLeray.Short.PartIIb.Sub.PartIIb_S3_1
import UnforcedLeray.Short.PartIIb.Tasks.StrongRegularity.JointSmooth.FirstOrderPhaseDeriv
import UnforcedLeray.Short.PartIIb.Tasks.StrongRegularity.JointSmooth.HigherOrderPhaseDeriv

/-!
# `PartII-b:S3/1` spacetime regularity bootstrap (`JointSmooth.lean`, SP 2559-2562)

Decomposed via `UnforcedLeray.Short.«PartII-b».Sub.«PartII-b_S3_1»`: once `PartII-b:S3/1/1`
(`bgFirstOrderPhaseDeriv_proof : BgFirstOrderPhaseDeriv` in
`UnforcedLeray.Short.«PartII-b».Tasks.StrongRegularity.JointSmooth.FirstOrderPhaseDeriv`) and
`PartII-b:S3/1/2` (`bgHigherOrderPhaseDerivTower_proof : BgHigherOrderPhaseDerivTower` in
`UnforcedLeray.Short.«PartII-b».Tasks.StrongRegularity.JointSmooth.HigherOrderPhaseDeriv`) are
proved, assemble:
```lean
theorem jointSmoothnessFromSpatialAllOrders_proof :
    UnforcedLeray.Short.IIb.JointSmoothnessFromSpatialAllOrders :=
  jointSmoothnessFromSpatialAllOrders_of
    bgFirstOrderPhaseDeriv_proof bgHigherOrderPhaseDerivTower_proof
```
-/

theorem jointSmoothnessFromSpatialAllOrders_proof :
    UnforcedLeray.Short.IIb.JointSmoothnessFromSpatialAllOrders :=
  UnforcedLeray.Short.IIb.jointSmoothnessFromSpatialAllOrders_of
    UnforcedLeray.Short.IIb.bgFirstOrderPhaseDeriv_proof bgHigherOrderPhaseDerivTower_proof
