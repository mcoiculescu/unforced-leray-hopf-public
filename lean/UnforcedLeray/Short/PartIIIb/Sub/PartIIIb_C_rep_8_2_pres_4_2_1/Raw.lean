import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_4_2_1.Org
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_4_2_1.Vel
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_4_2_1.Raised
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_4_2_1.Axis
import UnforcedLeray.Short.PartI.Tasks.OverlapHighNorm
import UnforcedLeray.Short.PartI.Tasks.OverlapFluctuationDecay
import UnforcedLeray.Short.PartI.Tasks.OverlapMeanPrimitive
import UnforcedLeray.Short.PartI.Tasks.OverlapMeanDecay
import UnforcedLeray.Short.PartI.Tasks.TrainOverlapProof
import UnforcedLeray.Short.PartI.Tasks.TrainVorticityTail
import UnforcedLeray.Short.PartI.Tasks.TrainStreamTails
import UnforcedLeray.Short.PartI.Tasks.TrainFluctuationDecayProof
import UnforcedLeray.Short.PartI.Tasks.TrainMeanExpansionProof

/-!
# `PartIII-b:C/rep/8/2/pres/4/2/1/1`: Sup bound of the raw background

Source of record: `the November 2 reference manuscript`,
lines 2715-2725 (`sup √s W|v| ≤ P_ν`), 5461-5463 (`U_raw = √s(v + εHe_z)`),
1205-1225 (lift smooth through the axis for large `n`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Short.PartI

/-- **Sup bound of the raw background** (`PartIII-b:C/rep/8/2/pres/4/2/1/1`,
source lines 2715-2725, 5461-5463, 1205-1225). -/
theorem rawSupBound (D : SeqData) {dm dp : Real} (hst : D.RepairStanding dm dp) : RawSupBound D := by
  have hHN : OverlapHighNormUniform := overlap_highnorm_uniform
  have hOFD : OverlapFluctuationDecay := overlap_fluctuation_decay hHN
  have hMP : OverlapMeanPrimitive := overlap_mean_primitive
  have hMD : OverlapMeanDecay := overlap_mean_decay hHN hOFD hMP
  have hOv : TrainOverlap := trainOverlap_proof hOFD hMD
  have hVort : TrainVorticityGaussianTail := train_vorticity_gaussian_tail hOv
  have hTails : TrainStreamVelocityPressureTails := train_stream_velocity_pressure_tails hOv hVort
  have hFD : TrainFluctuationDecay := trainFluctuationDecay_proof hTails hOFD hOv
  have hME : TrainMeanExpansion := trainMeanExpansion_proof hTails hFD hMP
  exact rawSupBound_of D hst (velWeightedSup_of D hst)
    (raisedWeightedSup_of hME hFD D hst) (rawAxisCont_eventually_of hME hFD D hst)

end UnforcedLeray.Short.PartIIIb.Concrete
