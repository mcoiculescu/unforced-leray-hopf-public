import UnforcedLeray.Short.Spine.Sub.SP_EST
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations
import UnforcedLeray.Short.PartI.Tasks.TrainComparisonProof
import UnforcedLeray.Short.PartI.Tasks.OverlapHighNorm
import UnforcedLeray.Short.PartI.Tasks.OverlapFluctuationDecay
import UnforcedLeray.Short.PartI.Tasks.OverlapMeanPrimitive
import UnforcedLeray.Short.PartI.Tasks.OverlapMeanDecay
import UnforcedLeray.Short.PartI.Tasks.TrainOverlapProof
import UnforcedLeray.Short.PartI.Tasks.TrainL2DecayProof
import UnforcedLeray.Short.PartI.Tasks.TrainStrainIntegralProof
import UnforcedLeray.Short.Spine.Proofs.TrainEstimates.FluctuationIntegral
import UnforcedLeray.Short.PartI.Tasks.TrainVorticityTail
import UnforcedLeray.Short.PartI.Tasks.TrainStreamTails
import UnforcedLeray.Short.PartI.Tasks.TrainFluctuationDecayProof
import UnforcedLeray.Short.PartI.Tasks.TrainMeanExpansionProof
import UnforcedLeray.Short.PartI.Tasks.TrainTransverseTailsProof
import UnforcedLeray.Short.PartI.Tasks.TrainFixedBandProof
import UnforcedLeray.Short.Spine.Proofs.EstVcRegularity
import UnforcedLeray.Short.Spine.Proofs.EstTrainPreError
import UnforcedLeray.Short.Spine.Proofs.EstTrainPostBound

/-!
# `Spine:SP-EST` (`TrainEstimates.lean`): all Part I train estimates and `TrainUniform`

Source of record: `the November 2 reference manuscript`,
Lemmas `sct:train` and `sct:heat` (lines 290-554) and line 2053.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.Spine

/-- **Main theorem (`Spine:SP-EST`)**: unconditional bundle of the ten Part I train estimates
(`PartITrainEstimates`, source lines 290-554) and the uniform derivative bound `TrainUniform`
(source line 2053). -/
theorem trainEstimates : UnforcedLeray.Short.Spine.TrainEstimatesAll := by
  have hHN : PartI.OverlapHighNormUniform := PartI.overlapHighNormUniform_proof
  have hFD : PartI.OverlapFluctuationDecay := PartI.overlap_fluctuation_decay hHN
  have hMP : PartI.OverlapMeanPrimitive := PartI.overlap_mean_primitive
  have hMD : PartI.OverlapMeanDecay := PartI.overlap_mean_decay hHN hFD hMP
  have hOv : PartI.TrainOverlap := PartI.trainOverlap_proof hFD hMD
  have hL2 : PartI.TrainL2Decay := PartI.trainL2Decay_proof hOv
  have hStrain : PartI.TrainStrainIntegral := PartI.trainStrainIntegral_proof hOv
  have hFluctInt : PartI.TrainFluctuationIntegral := trainFluctuationIntegral_proof hL2 hOv
  have hVort : PartI.TrainVorticityGaussianTail := PartI.train_vorticity_gaussian_tail hOv
  have hTails : PartI.TrainStreamVelocityPressureTails :=
    PartI.train_stream_velocity_pressure_tails hOv hVort
  have hFluctDecay : PartI.TrainFluctuationDecay :=
    PartI.trainFluctuationDecay_proof hTails hFD hOv
  have hExpansion : PartI.TrainMeanExpansion :=
    PartI.trainMeanExpansion_proof hTails hFluctDecay hMP
  have hTransTails : PartI.TrainTransverseTails :=
    PartI.trainTransverseTails_proof hVort hTails
  have hBand : PartI.TrainFixedBand := PartI.trainFixedBand_proof hTails hFluctDecay
  exact trainEstimates_of
    PartI.trainComparison_proof
    hOv
    hL2
    hStrain
    hFluctInt
    PartI.trainMeanEquations_proof
    hFluctDecay
    hExpansion
    hTransTails
    hBand
    vcRegularity_proof
    trainPreError_proof
    trainPostBound_proof

end UnforcedLeray.Short.Spine
