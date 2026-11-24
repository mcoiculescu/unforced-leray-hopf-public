import UnforcedLeray.Short.PartIIb.Sub.PartIIb_S3_1_comoving
import UnforcedLeray.Short.PartIIb.Tasks.StrongRegularity.JointSmooth.FirstOrderPhaseDeriv.PhaseDerivStep.ComovingEquation

/-!
# `PartII-b:S3/1/1/2` (`BgFirstPhaseDerivStep`, `PhaseDerivStep.lean`, SP 2519-2523, 2559-2562)

Source of record: `the November 2 reference manuscript`,
lines 2519-2523 and 2559-2562.

Decomposed along comoving rays via `UnforcedLeray.Short.«PartII-b».Sub.«PartII-b_S3_1_comoving»`:
the first comoving derivative is `U₁ = comovingEvolRHS p.ν (bgField p z) = νΔU + ½U - 𝔓(U·∇U)`.
Once `PartII-b:S3/1/1/2/1` (`bgComovingFirstEquation_proof : BgComovingFirstEquation` in
`UnforcedLeray.Short.«PartII-b».Tasks.StrongRegularity.JointSmooth.FirstOrderPhaseDeriv.PhaseDerivStep.ComovingEquation`)
is proved, import that module and assemble:
```lean
theorem bgFirstPhaseDerivStep_proof :
    UnforcedLeray.Short.IIb.BgFirstPhaseDerivStep :=
  bgFirstPhaseDerivStep_of_comoving bgComovingFirstEquation_proof
```
-/

theorem bgFirstPhaseDerivStep_proof :
    UnforcedLeray.Short.IIb.BgFirstPhaseDerivStep :=
  UnforcedLeray.Short.IIb.bgFirstPhaseDerivStep_of_comoving
    bgComovingFirstEquation_proof
