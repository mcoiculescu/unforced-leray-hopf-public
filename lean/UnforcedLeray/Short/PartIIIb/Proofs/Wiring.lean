import UnforcedLeray.Short.PartIIIb.Proofs.Wiring.Skeleton
import UnforcedLeray.Short.PartIIIb.Proofs.DeferredRepair
import UnforcedLeray.Short.PartIIIb.Proofs.DeferredYoungFlat
import UnforcedLeray.Short.PartIIIb.Proofs.Wiring.WardAffineSeq
import UnforcedLeray.Short.PartIIIb.Proofs.Wiring.Mode
import UnforcedLeray.Short.PartIIIb.Proofs.Wiring.Constants
import UnforcedLeray.Short.PartIIIb.Proofs.Wiring.BackgroundBridge
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.PLBound
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Continuity.Main
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.NearBody
import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Actual
import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Proofs.TrainEvolutionExists
import UnforcedLeray.Short.PartIIIb.Concrete.Standing.Instance
import UnforcedLeray.Short.PartIIIb.NearInst.Body.Proofs.ForcedColumn
import UnforcedLeray.Short.PartIIIa.Clock.FrameKernels
import UnforcedLeray.Short.PartIIIa.T19_PolyCausal
import UnforcedLeray.Short.PartIIIa.T21_FullClock
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal
import UnforcedLeray.Short.PartIIIa.T05_HardyKernel
import UnforcedLeray.Short.PartIIIa.T15_SepKernelBounds
import UnforcedLeray.Short.PartIIIa.T16_SepYoung
import UnforcedLeray.Short.PartIIIa.T23_StressExactSplit.T23_1
import UnforcedLeray.Short.PartIIIa.T23_StressExactSplit.T23_2
import UnforcedLeray.Short.PartIIIa.T23_StressExactSplit.T23_3
import UnforcedLeray.Short.PartIIIa.T23_StressExactSplit.T23_4
import UnforcedLeray.Short.PartIIa.ComposeNear
import UnforcedLeray.Short.PartIIa.Tasks.N01StressMaps
import UnforcedLeray.Short.PartIIa.Tasks.N04SmoothAdjoint
import UnforcedLeray.Short.PartIIa.Tasks.N06BandLimited
import UnforcedLeray.Short.PartIIb.Tasks.StrongRegularityProof
import UnforcedLeray.Short.Spine.Proofs.TrainEstimates

/-!
# `PartIII-b:IIIb-D5`: unconditional assembly of `Spine.PartIIIOutput`

Source of record: `the November 2 reference manuscript`, lines 5777-5985
(with 2316-2318, 2505-2524, 2664-2713, 5951-5954).

Instantiates `Wiring.partIIIOutputSeq_of_inputs` (`Short/PartIII-b/Proofs/Wiring/Skeleton.lean`)
with the compiled concrete suppliers of Part III-b, Part III-a, Part II-a, Part II-b, Part I,
and Spine.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Short

/-- **Part III output** (`PartIII-b:IIIb-D5`, source lines 5777-5985): unconditional proof of
`UnforcedLeray.Short.Spine.PartIIIOutput`. -/
theorem partIIIOutput_proof : UnforcedLeray.Short.Spine.PartIIIOutput := by
  have hCF : PartIIa.NearCompactFreeComparison :=
    PartIIa.nearCompactFreeComparison_of_parts
      PartIIa.nearBandLimited PartIIa.nearSmoothAdjointComparison
  have hPC : IIIa.PolyCausal :=
    IIIa.polyCausal IIIa.fullClockWeakForward IIIa.freeCausalExistsUnique IIIa.hardyKernel
  have hF : PartI.TrainFluctuationDecay := Spine.trainEstimates.1.2.2.2.2.2.2.1
  have hM : PartI.TrainMeanExpansion := Spine.trainEstimates.1.2.2.2.2.2.2.2.1
  have hE : PartI.TrainMeanEquations := PartI.trainMeanEquations_proof
  have hFT : NearInst.FlatTrainMultBound := NearInst.flatTrainMultBound_of hF hM hE
  have hDelta : NearInst.NearDeltaBoundC :=
    NearInst.Delta.nearDeltaBoundC_of
      NearInst.Delta.outPartitionSum
      NearInst.Delta.trainMultRestr
      NearInst.Delta.thinDiffMult
      NearInst.Delta.broadMult
      NearInst.Delta.rawStreamCompletion
      NearInst.Delta.repairCoeffBound
      (NearInst.Delta.flatFreeGainBound_of IIIa.freeCausalExistsUnique)
      (NearInst.Delta.Target.compactWindowBlock_of hCF PartIIa.nearStressMapExists
        IIIa.freeCausalExistsUnique)
      (NearInst.Delta.partialStripBlock_of IIIa.sepKernelBounds IIIa.sepYoung
        IIIa.freeCausalExistsUnique)
      (NearInst.Delta.youngEndResponse_of PartIIa.nearStressMapExists IIIa.sepKernelBounds
        IIIa.sepYoung IIIa.freeCausalExistsUnique)
      (NearInst.Delta.oldEndResponse_of PartIIa.nearStressMapExists IIIa.freeCausalExistsUnique)
      IIIa.rawCoeffEarly IIIa.rawCoeffLate IIIa.inletCoeffBounds IIIa.rawTransverseTail
      hFT
      (nearMaskedFreeBoundC_of_leaves PartIIa.nearStressMapExists IIIa.sepKernelBounds
        IIIa.sepYoung)
  have hNS : NearInst.NearSolverC :=
    nearSolverC_of_layers hDelta PartIIa.nearStressMapExists IIIa.sepKernelBounds IIIa.sepYoung
      hPC IIIa.freeCausalExistsUnique hF hM hE
  have hFC : NearInst.ForcedColumnC :=
    NearInst.Body.forcedColumnC_of_inputs hNS hFT
      NearInst.Delta.trainMultRestr
      NearInst.Delta.thinDiffMult
      NearInst.Delta.broadMult
      NearInst.Delta.rawStreamCompletion
      NearInst.Delta.repairCoeffBound
      IIIa.rawCoeffEarly IIIa.rawCoeffLate IIIa.inletCoeffBounds IIIa.rawTransverseTail
      hCF
  have hSt : Wiring.StandingInput :=
    repairStanding_concrete
      PartIIa.nearStressMapExists hCF IIb.strongRegularity_proof
      IIIa.sepKernelBounds IIIa.sepYoung hPC IIIa.freeCausalExistsUnique
      IIIa.rawCoeffEarly IIIa.rawCoeffLate IIIa.inletCoeffBounds IIIa.rawTransverseTail
      hF hM hE
  exact Wiring.partIIIOutputSeq_of_inputs
    errorFamilyBounds_concrete
    flatLimit_concrete
    plBound_concrete
    returnNormContinuity_concrete
    nearBody
    FlatSettingInst.isFlatDuhamelColumn_actual
    hSt
    wardAffineSeq
    modeOfReturn
    constantsExist
    Wiring.backgroundBridge
    hNS
    PartIIIb.nearOpsExistCC
    hFC
    hPC
    FlatSettingInst.trainEvolutionExists
    IIIa.planarFrameKernelsExist

end UnforcedLeray.Short.PartIIIb.Concrete
end
