import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_4_2_1_1_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_4_2_1_1_1.LateVel
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2_3.Pt.SupV
import UnforcedLeray.Short.PartI.Tasks.OverlapHighNorm
import UnforcedLeray.Short.PartI.Tasks.OverlapFluctuationDecay
import UnforcedLeray.Short.PartI.Tasks.OverlapMeanPrimitive
import UnforcedLeray.Short.PartI.Tasks.OverlapMeanDecay
import UnforcedLeray.Short.PartI.Tasks.TrainOverlapProof
import UnforcedLeray.Short.PartI.Tasks.TrainVorticityTail
import UnforcedLeray.Short.PartI.Tasks.TrainStreamTails
import UnforcedLeray.Short.PartI.Tasks.TrainFluctuationDecayProof
import UnforcedLeray.Short.PartI.Tasks.TrainMeanExpansionProof
import UnforcedLeray.Short.PartI.Tasks.TrainFixedBandProof

/-!
# `PartIII-b:C/rep/8/2/pres/4/2/1/1/1`: Weighted sup bound of the train velocity

Source of record: `the November 2 reference manuscript`,
lines 2715-2725 (`sup √s W|v| ≤ P_ν`, `W ≥ 1`).

Assembles `RawSupOrg.VelWeightedSup D` via `velWeightedSup_of_sub` from `supV_of` (young ages
`0 < s ≤ 1/ν`, using `trainFixedBand_proof`, `PartI:T25`) and `lateVelSup_of` (late ages
`s > 1/ν`, using `trainMeanExpansion_proof`, `PartI:T23`, and `trainFluctuationDecay_proof`,
`PartI:T22`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Short.PartI

/-- **Weighted sup bound of the train velocity** (`PartIII-b:C/rep/8/2/pres/4/2/1/1/1`,
source lines 2715-2725). -/
theorem velWeightedSup_of (D : SeqData) {dm dp : Real} (hst : D.RepairStanding dm dp) : RawSupOrg.VelWeightedSup D := by
  have hHN : OverlapHighNormUniform := overlap_highnorm_uniform
  have hOFD : OverlapFluctuationDecay := overlap_fluctuation_decay hHN
  have hMP : OverlapMeanPrimitive := overlap_mean_primitive
  have hMD : OverlapMeanDecay := overlap_mean_decay hHN hOFD hMP
  have hOv : TrainOverlap := trainOverlap_proof hOFD hMD
  have hVort : TrainVorticityGaussianTail := train_vorticity_gaussian_tail hOv
  have hTails : TrainStreamVelocityPressureTails := train_stream_velocity_pressure_tails hOv hVort
  have hFD : TrainFluctuationDecay := trainFluctuationDecay_proof hTails hOFD hOv
  have hME : TrainMeanExpansion := trainMeanExpansion_proof hTails hFD hMP
  have hFB : TrainFixedBand := trainFixedBand_proof hTails hFD
  exact velWeightedSup_of_sub D hst (supV_of hFB) (LateVelAux.lateVelSup_of hME hFD)

end UnforcedLeray.Short.PartIIIb.Concrete
