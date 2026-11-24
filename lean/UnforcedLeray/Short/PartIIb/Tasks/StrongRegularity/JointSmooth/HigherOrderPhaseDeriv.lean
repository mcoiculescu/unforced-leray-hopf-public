import UnforcedLeray.Short.PartIIb.Sub.PartIIb_S3_1_comoving
import UnforcedLeray.Short.PartIIb.Tasks.StrongRegularity.JointSmooth.HigherOrderPhaseDeriv.LerayComovingComm
import UnforcedLeray.Short.PartIIb.Tasks.StrongRegularity.JointSmooth.HigherOrderPhaseDeriv.ComovingLaplacian
import UnforcedLeray.Short.PartIIb.Tasks.StrongRegularity.JointSmooth.HigherOrderPhaseDeriv.ComovingConvect
import UnforcedLeray.Short.PartIIb.Tasks.StrongRegularity.JointSmooth.FirstOrderPhaseDeriv.PhaseDerivStep.ComovingEquation

/-!
# `PartII-b:S3/1/2` comoving phase-derivative tower (`HigherOrderPhaseDeriv.lean`)

Source of record: `the November 2 reference manuscript`,
lines 2519-2523 and 2559-2562.

Decomposed along comoving rays via `UnforcedLeray.Short.«PartII-b».Sub.«PartII-b_S3_1_comoving»`
(`bgHigherOrderPhaseDerivTower_of_comoving`, tower `m ↦ comovingDerivOf^[m] (bgField p z)`).
Once `PartII-b:S3/1/2/3` (`smoothLerayComovingComm_proof` in
`...JointSmooth.HigherOrderPhaseDeriv.LerayComovingComm`), `PartII-b:S3/1/2/4`
(`comovingLaplacianRule_proof` in `...JointSmooth.HigherOrderPhaseDeriv.ComovingLaplacian`),
`PartII-b:S3/1/2/5` (`comovingConvectRule_proof` in
`...JointSmooth.HigherOrderPhaseDeriv.ComovingConvect`) and `PartII-b:S3/1/1/2/1`
(`bgComovingFirstEquation_proof` in
`...JointSmooth.FirstOrderPhaseDeriv.PhaseDerivStep.ComovingEquation`) are proved, import those
modules and assemble:
```lean
theorem bgHigherOrderPhaseDerivTower_proof :
    UnforcedLeray.Short.IIb.BgHigherOrderPhaseDerivTower :=
  bgHigherOrderPhaseDerivTower_of_comoving smoothLerayComovingComm_proof
    comovingLaplacianRule_proof comovingConvectRule_proof bgComovingFirstEquation_proof
```
-/

theorem bgHigherOrderPhaseDerivTower_proof :
    UnforcedLeray.Short.IIb.BgHigherOrderPhaseDerivTower :=
  UnforcedLeray.Short.IIb.bgHigherOrderPhaseDerivTower_of_comoving
    smoothLerayComovingComm_proof
    comovingLaplacianRule_proof
    comovingConvectRule_proof
    bgComovingFirstEquation_proof
