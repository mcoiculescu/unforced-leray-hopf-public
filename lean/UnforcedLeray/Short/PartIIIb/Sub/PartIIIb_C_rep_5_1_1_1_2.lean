import UnforcedLeray.Short.PartIIIb.NearInst.Proofs.NearOpsExist
import UnforcedLeray.Short.PartIIIb.NearInst.Proofs.CoeffMult
import UnforcedLeray.Short.PartIIIb.NearInst.Proofs.SplitMult
import UnforcedLeray.Short.PartIIIb.NearInst.FlatTrain.Proof
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Exists
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.StressMapReal
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.TepsReal
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.TensorTestDense
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.TensorTestDivMem
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.FarMaskExists
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.BoxDenseZ
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_2_Exists
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_2_Unique
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_2

/-!
# `PartIII-b:C/rep/5/1/1/1/2`: `NearInst.NearOpsExistC` from the primitive source lemmas

Source 3427-3440, 3866-3914, 1675-1690.  `nearOpsExistCC_of` reduces `NearOpsExistC` to the
primitive existence lemmas (all other ingredients are closed theorems):
`FreeCausalExistsUnique` (Part III-a), `FreeStressPinLinear`, `FreeStressPinBound` (each closed
(`freeStressPinLinear_proof`, `freeStressPinBound_proof`) but their proof files import
disjoint copies of the same `FlatFreeGain` declarations), `NearStressMapExists` (Part II-a, 1678-1690),
`CellPtHT`, `CellPtInvH`, `CellPtH` (each closed, but their proof files define the same `ctT` and cannot be
imported together), `FarKernelL2`, `FarKernelLinear` (far kernel, Masked), `TrainFluctuationDecay`,
`TrainMeanExpansion`, `TrainMeanEquations` (Part I), `StressCoefficients` (Part III-a).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.NearInst

theorem nearOpsExistCC_of (hU : UnforcedLeray.Short.IIIa.FreeCausalExistsUnique)
    (hN : UnforcedLeray.Short.PartIIa.NearStressMapExists)
    (hLin : FreeStressPinLinear) (hBd : FreeStressPinBound)
    (hT : ∀ c : ℝ, 0 < c → Masked.CellPtHT c) (hH : ∀ c : ℝ, 0 < c → Masked.CellPtInvH c)
    (hH' : ∀ c : ℝ, 0 < c → Masked.CellPtH c)
    (hL : Masked.FarKernelL2) (hA : Masked.FarKernelLinear)
    (hF : UnforcedLeray.Short.PartI.TrainFluctuationDecay)
    (hM : UnforcedLeray.Short.PartI.TrainMeanExpansion)
    (hE : UnforcedLeray.Short.PartI.TrainMeanEquations)
    (hSC : UnforcedLeray.Short.IIIa.StressCoefficients) : NearOpsExistC :=
  nearOpsExistC_of
    (freeStressExists_of (freeStressPinExists_of hU) (freeStressPinUnique_of hU)
      hLin hBd)
    (Masked.maskedNearExists_of hN
      (Masked.stressMapReal_of Masked.tepsReal Masked.tensorTestDense Masked.tensorTestDivMem)
      hT hH hH'
      (Masked.farMaskExists_of hL hA Masked.boxDenseZ))
    coeffMultExists (flatTrainMultBound_of hF hM hE) (splitMultBound_of hSC)

end UnforcedLeray.Short.PartIIIb.NearInst
