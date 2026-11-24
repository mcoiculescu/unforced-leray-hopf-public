import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_1_1_2.CoImport
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal
import UnforcedLeray.Short.PartIIa.Tasks.N01StressMaps
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.FarKernelL2
import UnforcedLeray.Short.PartIIIa.T15_SepKernelBounds
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.FarKernelLinear
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
import UnforcedLeray.Short.PartIIIa.T23_StressExactSplit.T23

/-!
# `PartIII-b:C/rep/5/1/1/1/2`: `NearOpsExistC` unconditionally

Source `the November 2 reference manuscript` lines 3427-3440, 3866-3914,
1675-1690. Assembles `nearOpsExistCC : NearInst.NearOpsExistC` from
`NearInst.nearOpsExistCC_of'` (`Sub/PartIII-b_C_rep_5_1_1_1_2/CoImport.lean`) and the eight
unconditional leaf theorems.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb

theorem nearOpsExistCC : NearInst.NearOpsExistC := by
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
  exact NearInst.nearOpsExistCC_of'
    UnforcedLeray.Short.IIIa.freeCausalExistsUnique
    UnforcedLeray.Short.PartIIa.nearStressMapExists
    (NearInst.Masked.farKernelL2_of UnforcedLeray.Short.IIIa.sepKernelBounds)
    NearInst.Masked.farKernelLinear
    hF
    hM
    UnforcedLeray.Short.PartI.trainMeanEquations_proof
    UnforcedLeray.Short.IIIa.stressSpacesExactSplit.1

end UnforcedLeray.Short.PartIIIb
