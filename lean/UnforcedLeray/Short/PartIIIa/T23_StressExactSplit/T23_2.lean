import UnforcedLeray.Short.PartIIIa.Sub.T23_2_org
import UnforcedLeray.Short.PartIIIa.T23_StressExactSplit.T23_2_1
import UnforcedLeray.Short.PartIIIa.T23_StressExactSplit.T23_2_2
import UnforcedLeray.Short.PartIIa.Tasks.R01.EarlyStreamProfile
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
# Part III-a, task `PartIII-a:T23/2`: early raw coefficient bounds (`RawCoeffEarly`)

Source of record: `the November 2 reference manuscript`, lines 2711-2738
(`stress-short:coefficients` at ages `0 < s ≤ 1`).

Assembles `rawCoeffEarly` from `rawCoeffEarly_of` (`Sub/T23_2_org.lean`), the two leaf theorems
(`earlyVel_of`, `earlyCompletion_of`), the Part II-a early stream profile (`earlyStreamProfile_of`,
`lateProfileSmooth_of`), and the Part I proofs (`trainFluctuationDecay_proof`,
`trainMeanExpansion_proof`, `trainStreamSmooth`).
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.IIIa

theorem rawCoeffEarly : UnforcedLeray.Short.IIIa.RawCoeffEarly := by
  have hHN : PartI.OverlapHighNormUniform := PartI.overlap_highnorm_uniform
  have hFD0 : PartI.OverlapFluctuationDecay := PartI.overlap_fluctuation_decay hHN
  have hMP : PartI.OverlapMeanPrimitive := PartI.overlap_mean_primitive
  have hMD : PartI.OverlapMeanDecay := PartI.overlap_mean_decay hHN hFD0 hMP
  have hOv : PartI.TrainOverlap := PartI.trainOverlap_proof hFD0 hMD
  have hVort : PartI.TrainVorticityGaussianTail := PartI.train_vorticity_gaussian_tail hOv
  have hTails : PartI.TrainStreamVelocityPressureTails :=
    PartI.train_stream_velocity_pressure_tails hOv hVort
  have hFD : PartI.TrainFluctuationDecay := PartI.trainFluctuationDecay_proof hTails hFD0 hOv
  have hME : PartI.TrainMeanExpansion := PartI.trainMeanExpansion_proof hTails hFD hMP
  have hS := PartI.trainStreamSmooth
  have hE : PartIIa.EarlyStreamProfile :=
    PartIIa.earlyStreamProfile_of hFD hME (PartIIa.lateProfileSmooth_of hS)
  exact rawCoeffEarly_of (earlyVel_of hE hS) (earlyCompletion_of hE hS)

end UnforcedLeray.Short.IIIa
