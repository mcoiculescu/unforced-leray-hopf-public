import UnforcedLeray.Short.PartIIa.Sub.R01
import UnforcedLeray.Short.PartIIa.Tasks.R01.EarlyStreamProfile
import UnforcedLeray.Short.PartIIa.Tasks.R01.EarlyPressureProfile
import UnforcedLeray.Short.PartIIa.Tasks.R01.EarlyCalculus
import UnforcedLeray.Short.PartIIa.Tasks.R01.EarlyA1
import UnforcedLeray.Short.PartIIa.Tasks.R01.EarlyA2
import UnforcedLeray.Short.PartIIa.Tasks.R01.EarlyB1
import UnforcedLeray.Short.PartIIa.Tasks.R01.EarlyB2
import UnforcedLeray.Short.PartIIa.Tasks.R01.EarlyB3
import UnforcedLeray.Short.PartIIa.Tasks.R02.ProfileSmooth
import UnforcedLeray.Short.PartI.Tasks.OverlapHighNorm
import UnforcedLeray.Short.PartI.Tasks.OverlapFluctuationDecay
import UnforcedLeray.Short.PartI.Tasks.OverlapMeanPrimitive
import UnforcedLeray.Short.PartI.Tasks.OverlapMeanDecay
import UnforcedLeray.Short.PartI.Tasks.TrainOverlapProof
import UnforcedLeray.Short.PartI.Tasks.TrainVorticityTail
import UnforcedLeray.Short.PartI.Tasks.TrainStreamTails
import UnforcedLeray.Short.PartI.Tasks.TrainFluctuationDecayProof
import UnforcedLeray.Short.PartI.Tasks.TrainMeanExpansionProof
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations.StreamSmooth

/-!
# Part II-a, task `PartII-a:R01`: the early residual table (unconditional assembly)

Source of record: `the November 2 reference manuscript`, lines 1294-1297 ("at zero
age the integrands are bounded"), with Lemma `sct:heat` (lines 437-481: `sct:fluctuation` 439-446,
`sct:expansion` 447-459, read at ages `0 < s ≤ 1`).

Assembles `ringEarlyBound : RingEarlyBound` from `ringEarlyBound_of` (`Sub/R01.lean`), the leaf
blocks `ringEarlyA1_of`, `ringEarlyA2_of`, `ringEarlyB1_of`, `ringEarlyB2_of`, `ringEarlyB3_of`,
`earlyCalculus`, `earlyStreamProfile_of`, `earlyPressureProfile_of`, `lateProfileSmooth_of`, and
the Part I train estimates (`TrainFluctuationDecay`, `TrainMeanExpansion`, `TrainStreamSmooth`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIa

/-- **`PartII-a:R01`: the early residual bound** (source lines 1294-1297). -/
theorem ringEarlyBound : RingEarlyBound := by
  have hOFluct : UnforcedLeray.Short.PartI.OverlapFluctuationDecay :=
    UnforcedLeray.Short.PartI.overlap_fluctuation_decay
      UnforcedLeray.Short.PartI.overlap_highnorm_uniform
  have hOMean : UnforcedLeray.Short.PartI.OverlapMeanDecay :=
    UnforcedLeray.Short.PartI.overlap_mean_decay
      UnforcedLeray.Short.PartI.overlap_highnorm_uniform hOFluct
      UnforcedLeray.Short.PartI.overlap_mean_primitive
  have hOv : UnforcedLeray.Short.PartI.TrainOverlap :=
    UnforcedLeray.Short.PartI.trainOverlap_proof hOFluct hOMean
  have hVort : UnforcedLeray.Short.PartI.TrainVorticityGaussianTail :=
    UnforcedLeray.Short.PartI.train_vorticity_gaussian_tail hOv
  have hTails : UnforcedLeray.Short.PartI.TrainStreamVelocityPressureTails :=
    UnforcedLeray.Short.PartI.train_stream_velocity_pressure_tails hOv hVort
  have hFD : UnforcedLeray.Short.PartI.TrainFluctuationDecay :=
    UnforcedLeray.Short.PartI.trainFluctuationDecay_proof hTails hOFluct hOv
  have hME : UnforcedLeray.Short.PartI.TrainMeanExpansion :=
    UnforcedLeray.Short.PartI.trainMeanExpansion_proof hTails hFD
      UnforcedLeray.Short.PartI.overlap_mean_primitive
  have hS : LateProfileSmooth :=
    lateProfileSmooth_of UnforcedLeray.Short.PartI.trainStreamSmooth
  have hψ : EarlyStreamProfile := earlyStreamProfile_of hFD hME hS
  have hp : EarlyPressureProfile := earlyPressureProfile_of hFD hS
  exact ringEarlyBound_of (ringEarlyA1_of earlyCalculus hψ hp hS)
    (ringEarlyA2_of earlyCalculus hψ hp hS)
    (ringEarlyB1_of earlyCalculus hψ hp hS)
    (ringEarlyB2_of earlyCalculus hψ hp hS)
    (ringEarlyB3_of earlyCalculus hψ hp hS)

end UnforcedLeray.Short.PartIIa
