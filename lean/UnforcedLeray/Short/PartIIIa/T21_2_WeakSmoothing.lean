import UnforcedLeray.Short.PartIIIa.Clock.WeakSmoothing.PhysFromMoving
import UnforcedLeray.Short.PartIIIa.Clock.WeakSmoothing.MovingOfAdjoint
import UnforcedLeray.Short.PartIIIa.Clock.WeakSmoothing.LocalizedBound
import UnforcedLeray.Short.PartIIIa.Clock.WeakSmoothing.EnergyIneqs
import UnforcedLeray.Short.PartIIIa.Clock.WeakSmoothing.PairingBound
import UnforcedLeray.Short.PartIIIa.Clock.WeakSmoothing.TerminalBound
import UnforcedLeray.Short.PartIIIa.Clock.WeakSmoothing.WeightLogBounds
import UnforcedLeray.Short.PartIIIa.Clock.WeakSmoothing.RescaledTrain
import UnforcedLeray.Short.PartIIIa.Clock.WeakSmoothing.AdjointExists
import UnforcedLeray.Short.PartIIIa.Clock.WeakSmoothing.EnergyChain
import UnforcedLeray.Short.PartIIIa.Clock.WeakSmoothing.XNormDuality
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_6.TrainWeightedJetPoly
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_6.FluctJetWeighted
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_6.MeanJetWeighted
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_6.MeanVecFormula
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_6.MeanStreamJetBound
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_6.VcWeightedJet
import UnforcedLeray.Short.PartI.Tasks.TrainComparisonProof
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

/-!
# Part III-a, task `PartIII-a:T21/2`: physical weak smoothing (`WeakSmoothingPhys`)

Source of record: `the November 2 reference manuscript`, lines 3040-3084, 270-288.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.IIIa

theorem weakSmoothingPhys (m : ℝ) (hm : 8 < m) (hS : ScalingBounds) : WeakSmoothingPhys m := by
  have hcmp : PartI.TrainComparison := PartI.trainComparison_proof
  have hHN : PartI.OverlapHighNormUniform := PartI.overlap_highnorm_uniform
  have hFD0 : PartI.OverlapFluctuationDecay := PartI.overlap_fluctuation_decay hHN
  have hMP : PartI.OverlapMeanPrimitive := PartI.overlap_mean_primitive
  have hMD : PartI.OverlapMeanDecay := PartI.overlap_mean_decay hHN hFD0 hMP
  have hOv : PartI.TrainOverlap := PartI.trainOverlap_proof hFD0 hMD
  have hVort : PartI.TrainVorticityGaussianTail := PartI.train_vorticity_gaussian_tail hOv
  have hTails : PartI.TrainStreamVelocityPressureTails :=
    PartI.train_stream_velocity_pressure_tails hOv hVort
  have hfl : PartI.TrainFluctuationDecay := PartI.trainFluctuationDecay_proof hTails hFD0 hOv
  have hme : PartI.TrainMeanExpansion := PartI.trainMeanExpansion_proof hTails hfl hMP
  have hmeq : PartI.TrainMeanEquations := PartI.trainMeanEquations_proof
  have hT : RescaledTrainBounds m := rescaledTrainBounds m hcmp hfl hme hmeq
  have hW : TrainWeightedJetPoly :=
    trainWeightedJetPoly_of (fluctJetWeighted_of hfl)
      (meanJetWeighted_of (meanVecFormula_of hmeq) (meanStreamJetBound_of hme hmeq)) vcWeightedJet
  exact weakSmoothingPhys_of_moving m (by linarith) hS
    (movingWeakStrong_of m adjointEnergyChain
      (adjointEnergyIneqs m hm periodicWeightLogBounds hT (adjointLocalizedBound m hm hT) hW)
      ⟨xNormDuality m, adjointTerminalBound m (by linarith), adjointPairingBound m hm hW⟩
      (adjointExists m hm hW))

end UnforcedLeray.Short.IIIa
