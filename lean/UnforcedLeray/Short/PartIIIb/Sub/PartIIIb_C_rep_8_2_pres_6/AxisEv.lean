import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_6_axis
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_6_axis.NvLimit
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_6_axis.TrainDecay
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
# `PartIII-b:C/rep/8/2/pres/6/axis`: unconditional assembly of `AxisEv`

Source `the November 2 reference manuscript`:
lines 1205-1235, 1310-1323 (smooth through the axis from the full heat expansion), 437-467
(`sct:heat`). Assembles `axisEv` from `axisEv_of`, `axisEvNvLimit`, `axisEvTrainDecay_of`, and the
unconditional Part I train estimates (`PartI:T22`, `PartI:T23`, `PartI:T01`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **`PartIII-b:C/rep/8/2/pres/6/axis`: eventual axis continuity of the raw lift**
(source 1205-1235, 1310-1323, 437-467). -/
theorem axisEv (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) : AxisEv D dm dp := by
  have hHN : PartI.OverlapHighNormUniform := PartI.overlap_highnorm_uniform
  have hFD0 : PartI.OverlapFluctuationDecay := PartI.overlap_fluctuation_decay hHN
  have hMP : PartI.OverlapMeanPrimitive := PartI.overlap_mean_primitive
  have hMD : PartI.OverlapMeanDecay := PartI.overlap_mean_decay hHN hFD0 hMP
  have hOv : PartI.TrainOverlap := PartI.trainOverlap_proof hFD0 hMD
  have hVort : PartI.TrainVorticityGaussianTail := PartI.train_vorticity_gaussian_tail hOv
  have hTails : PartI.TrainStreamVelocityPressureTails :=
    PartI.train_stream_velocity_pressure_tails hOv hVort
  have hF : PartI.TrainFluctuationDecay := PartI.trainFluctuationDecay_proof hTails hFD0 hOv
  have hM : PartI.TrainMeanExpansion := PartI.trainMeanExpansion_proof hTails hF hMP
  exact axisEv_of D hst axisEvNvLimit
    (axisEvTrainDecay_of hF hM PartI.trainMeanEquations_proof)

end UnforcedLeray.Short.PartIIIb.Concrete
