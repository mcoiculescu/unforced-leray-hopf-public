import UnforcedLeray.Short.PartIIb.Sub.PartIIb_S3_1_comoving
import UnforcedLeray.Short.PartIIb.Tasks.StrongRegularity.JointSmooth.FirstOrderPhaseDeriv.PhaseDerivStep.ComovingEquation.JointSmoothPartial
import UnforcedLeray.Short.PartIIb.Tasks.StrongRegularity.JointSmooth.FirstOrderPhaseDeriv.PhaseDerivStep.ComovingEquation.CorrComovingDeriv
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletSourcePtw.Fields.RawJointSmooth

/-!
# `PartII-b:S3/1/1/2/1` (`BgComovingFirstEquation`, `ComovingEquation.lean`, SP 2519-2523, 2559-2562)

Source of record: `the November 2 reference manuscript`,
lines 2519-2523 and 2559-2562.

`T₀U = νΔU + ½U - 𝔓(U·∇U)` along comoving rays, split as `U = U_raw + E_εα + w`
(`bgComovingFirstEquation_of` in `UnforcedLeray.Short.«PartII-b».Sub.«PartII-b_S3_1_comoving»`).
Once `PartII-b:S3/1/1/2/1/3` (`jointSmoothComovingPartial_proof : JointSmoothComovingPartial` in
`...PhaseDerivStep.ComovingEquation.JointSmoothPartial`) and `PartII-b:S3/1/1/2/1/2`
(`bgCorrComovingJetDeriv_proof : BgCorrComovingJetDeriv` in
`...PhaseDerivStep.ComovingEquation.CorrComovingDeriv`) are proved, import those modules and
`UnforcedLeray.Short.«PartII-b».Tasks.AffineColumnComparison.InletSourcePtw.Fields.RawJointSmooth`
(accepted `PartII-b:G4/4/1/1/2`) and assemble:
```lean
theorem bgComovingFirstEquation_proof :
    UnforcedLeray.Short.IIb.BgComovingFirstEquation :=
  bgComovingFirstEquation_of rawJointSmooth
    jointSmoothComovingPartial_proof bgCorrComovingJetDeriv_proof
```
-/

theorem bgComovingFirstEquation_proof :
    UnforcedLeray.Short.IIb.BgComovingFirstEquation :=
  UnforcedLeray.Short.IIb.bgComovingFirstEquation_of
    UnforcedLeray.Short.IIb.rawJointSmooth
    jointSmoothComovingPartial_proof
    UnforcedLeray.Short.IIb.bgCorrComovingJetDeriv_proof
