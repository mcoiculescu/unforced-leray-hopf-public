import UnforcedLeray.Short.PartIIIa.Sub.T23_1_org
import UnforcedLeray.Short.PartIIIa.T23_StressExactSplit.T23_1.LateFluctVel
import UnforcedLeray.Short.PartIIIa.T23_StressExactSplit.T23_1.LateMeanVel
import UnforcedLeray.Short.PartIIIa.T23_StressExactSplit.T23_1.LateFluctCompletion
import UnforcedLeray.Short.PartIIIa.T23_StressExactSplit.T23_1.LateMeanCompletion
import UnforcedLeray.Short.PartIIIa.T23_StressExactSplit.T23_1.RaisedStreamSplit
import UnforcedLeray.Short.PartI.Tasks.OverlapHighNorm
import UnforcedLeray.Short.PartI.Tasks.OverlapFluctuationDecay
import UnforcedLeray.Short.PartI.Tasks.OverlapMeanPrimitive
import UnforcedLeray.Short.PartI.Tasks.OverlapMeanDecay
import UnforcedLeray.Short.PartI.Tasks.TrainOverlapProof
import UnforcedLeray.Short.PartI.Tasks.TrainVorticityTail
import UnforcedLeray.Short.PartI.Tasks.TrainStreamTails
import UnforcedLeray.Short.PartI.Tasks.TrainFluctuationDecayProof
import UnforcedLeray.Short.PartI.Tasks.TrainMeanExpansionProof
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations.StreamSmooth
import UnforcedLeray.Short.PartIIa.Sub.R01_1
import UnforcedLeray.Short.PartIIa.Tasks.R02.ProfileSmooth
import UnforcedLeray.Short.PartIIa.Tasks.R01.EarlyStreamProfile.MeanStreamSmooth
import UnforcedLeray.Short.PartIIa.Tasks.R02.MeanRemainder.SliceDerivContinuous
import UnforcedLeray.Short.PartIIa.Tasks.R02.FluctuationProfile.AgeDerivSmooth
import UnforcedLeray.Short.PartIIa.Tasks.R02.MeanRemainder.EssSupPointwise

/-!
# Part III-a, task `PartIII-a:T23/1`: late raw coefficient bounds (`RawCoeffLate`)

Source of record: `the November 2 reference manuscript`, lines 2703-2727.

Assembles `rawCoeffLate` from `rawCoeffLate_of` (`Sub/T23_1_org.lean`), the five leaf theorems
(`lateFluctVel_of`, `lateMeanVel_of`, `lateFluctCompletion_of`, `lateMeanCompletion_of`,
`raisedStreamSplit_of`), the Part I proofs (`trainFluctuationDecay_proof`,
`trainMeanExpansion_proof`, `trainMeanEquations_proof`, `trainStreamSmooth`), and the Part II-a
smoothness and pointwise stream bounds (`lateProfileSmooth_of`, `meanStreamSmooth_of`,
`meanStreamPointwise_of`, `sliceDerivContinuous_of`, `ageDerivSmooth`, `essSupPointwise`).
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.IIIa

theorem rawCoeffLate : UnforcedLeray.Short.IIIa.RawCoeffLate := by
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
  have hSm := PartIIa.meanStreamSmooth_of (PartIIa.lateProfileSmooth_of hS)
  have hP := PartIIa.meanStreamPointwise_of hME hSm
    (PartIIa.sliceDerivContinuous_of PartIIa.ageDerivSmooth) PartIIa.essSupPointwise
  exact rawCoeffLate_of (lateFluctVel_of hFD)
    (lateMeanVel_of PartI.trainMeanEquations_proof hP)
    (lateFluctCompletion_of hFD hSm)
    (lateMeanCompletion_of hP)
    (raisedStreamSplit_of hS hSm)

end UnforcedLeray.Short.IIIa
