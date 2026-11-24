import UnforcedLeray.Short.PartIIb.Tasks.StrongRegularity.JointSmooth.FirstOrderPhaseDeriv.PhaseDerivStep.ComovingEquation.CorrComovingDeriv.Continuity
import UnforcedLeray.Short.PartIIb.Tasks.StrongRegularity.JointSmooth.FirstOrderPhaseDeriv.PhaseDerivStep.ComovingEquation.CorrComovingDeriv.BaseRep
import UnforcedLeray.Short.PartIIb.Tasks.StrongRegularity.JointSmooth.FirstOrderPhaseDeriv.PhaseDerivStep.ComovingEquation.CorrComovingDeriv.LerayCont

/-!
# Joint jets of the comoving correction (`PartII-b:S3/1/1/2/1/2`)

Source of record: `the November 2 reference manuscript`,
lines 2519-2523, 2559-2562. Composition of the base `T₀`-identification
(`corrT0BaseRep_proof`) and the joint continuity of the Leray term (`lerayJetContinuous_proof`).
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.IIb

theorem bgCorrComovingJetDeriv_proof : UnforcedLeray.Short.IIb.BgCorrComovingJetDeriv :=
  UnforcedLeray.Short.IIb.CorrComovingSub.bgCorrComovingJetDeriv_of_base_leray
    corrT0BaseRep_proof lerayJetContinuous_proof

end UnforcedLeray.Short.IIb
