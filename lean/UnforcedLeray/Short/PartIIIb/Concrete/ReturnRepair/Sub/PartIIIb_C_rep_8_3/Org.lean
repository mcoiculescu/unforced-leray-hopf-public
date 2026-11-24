import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_3.Split
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_3.GaussSum
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_3.TrainPt
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_3.RingSub
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_3.TrainCell
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_3.RingPt
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_3.TrainSlice
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_3.Meas
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.ActualJet
import UnforcedLeray.Short.PartI.Tasks.OverlapHighNorm
import UnforcedLeray.Short.PartI.Tasks.OverlapFluctuationDecay
import UnforcedLeray.Short.PartI.Tasks.OverlapMeanPrimitive
import UnforcedLeray.Short.PartI.Tasks.OverlapMeanDecay
import UnforcedLeray.Short.PartI.Tasks.TrainOverlapProof
import UnforcedLeray.Short.PartI.Tasks.TrainVorticityTail
import UnforcedLeray.Short.PartI.Tasks.TrainStreamTails
import UnforcedLeray.Short.PartI.Tasks.TrainFluctuationDecayProof
import UnforcedLeray.Short.PartI.Tasks.TrainFixedBandProof

/-!
# `PartIII-b:C/rep/8/3/2`: `GRBound` assembly (`grBound_proof`, source 5484-5498)

Source of record: `the November 2 reference manuscript`, lines 5484-5498.
Assembles `grBound_proof` from `grBound_of` (`Split.lean`), the Gaussian-replacement leaves,
`actualJet`, `grMeas_proof`, and `trainFixedBand_proof` (`PartI:T25`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **`PartIII-b:C/rep/8/3/2`**: Gaussian replacement bound `GRBound` (source 5484-5498). -/
theorem grBound_proof (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) : D.GRBound := by
  have hHN := UnforcedLeray.Short.PartI.overlap_highnorm_uniform
  have hOFD := UnforcedLeray.Short.PartI.overlap_fluctuation_decay hHN
  have hOMP := UnforcedLeray.Short.PartI.overlap_mean_primitive
  have hOMD := UnforcedLeray.Short.PartI.overlap_mean_decay hHN hOFD hOMP
  have hOv := UnforcedLeray.Short.PartI.trainOverlap_proof hOFD hOMD
  have hVort := UnforcedLeray.Short.PartI.train_vorticity_gaussian_tail hOv
  have hTails := UnforcedLeray.Short.PartI.train_stream_velocity_pressure_tails hOv hVort
  have hFD := UnforcedLeray.Short.PartI.trainFluctuationDecay_proof hTails hOFD hOv
  have hF := UnforcedLeray.Short.PartI.trainFixedBand_proof hTails hFD
  exact grBound_of D hst gaussSumEA ringAffGenSub ringAffGenPt trainSliceSmooth
    (trainGaussCell_of hF trainGaussPt) (affMJet_of D hst (actualJet D hst)) (grMeas_proof D)

end UnforcedLeray.Short.PartIIIb.Concrete
