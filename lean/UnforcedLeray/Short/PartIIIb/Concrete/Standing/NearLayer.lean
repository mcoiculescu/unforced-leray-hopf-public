import UnforcedLeray.Short.PartIIIb.NearInst.Proofs.NearSolver
import UnforcedLeray.Short.PartIIIb.NearInst.Proofs.NearFlat
import UnforcedLeray.Short.PartIIIb.NearInst.FlatTrain.Proof
import UnforcedLeray.Short.PartIIIa.ComposeCorollary
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Bound
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.MaskedLowerPiece
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.MaskedBinPiece
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.MaskedUpperPiece
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.OutBandPartition
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.RealStressBound
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.StressMapUnique
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.StressTransportNorm
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.MaskedSupport
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.ForbiddenBlockBound
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.ForbiddenKernelBound
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.GainBlockBound
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.FarBlockZero
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.MaskedStripBound
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.StripKernelBound
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.FarUpperZero
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.StressKernelRealization
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.BoxDenseZ
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.TensorTestDense
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.TensorTestDivMem
import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.CompactWindow.Comparison.FlatStress.CellPtChangeAll

/-!
# The near layer composed down to its inputs (`ORG:C/standing` (b))

Source of record: `the November 2 reference manuscript` (73 pages).

`NearSolverC` (`near:inverse-comparison` under the parameter choice, source 3943-3951,
4109-4124) is `nearSolverC_of` (`PartIII-b:C/near/6`) of `NearFlatBoundC` (`near:flat-bound`,
3881-3887, `PartIII-b:C/near/3`), `NearDeltaBoundC` (`near:deltaN`, 3927-3942, open
`PartIII-b:C/near/delta`) and `NearMaskedFreeBoundC` (`near:masked-free-bound`, 4023-4031,
`PartIII-b:C/near/masked-bound`).  Here every accepted `X_of` of the flat and masked branches is
composed with its accepted leaves:

* `nearMaskedFreeBoundC_of_leaves` : from `PartIIa.NearStressMapExists` (`PartII-a:N01`),
  `IIIa.SepKernelBounds` (`PartIII-a:T15`) and `IIIa.SepYoung`, through
  `maskedLowerPiece_of`, `maskedBinPiece_of`, `maskedUpperPiece_of`, `outBandPartition`,
  `realStressBound_of`, `stressMapUnique_of`, `stressTransportNorm_of`, `maskedSupport_of`,
  `forbiddenBlockBound_of`, `forbiddenKernelBound_of`, `gainBlockBound`, `farBlockZero_of`,
  `maskedStripBound_of`, `stripKernelBound_of`, `farUpperZero_of`, `stressKernelRealization`,
  `boxDenseZ`, `tensorTestDense`, `tensorTestDivMem`, `cpcHT_eq`, `cpcH_eq`
  (`PartIII-b:C/near/masked/6-30`);
* `nearFlatBoundC_of_leaves` : from `IIIa.PolyCausal` (with `polyStressCorollary_of_polyCausal`),
  `IIIa.FreeCausalExistsUnique` and the train statements `PartI.TrainFluctuationDecay`,
  `PartI.TrainMeanExpansion`, `PartI.TrainMeanEquations` (`flatTrainMultBound_of`,
  `PartIII-b:C/near/flat-train`);
* `nearSolverC_of_layers` : `NearSolverC` from these and `NearDeltaBoundC`.

The delta branch (`nearDeltaBoundC_of`, `NearInst/Delta/Assembly.lean`, open
`PartIII-b:C/near/delta`; on 2026-11-06 that file does not compile, line 456) is composed with its
leaves in the task `PartIII-b:C/standing` (`Concrete/Standing/Instance.lean`), with the open
leaves `RawStreamCompletion` (`PartIII-b:C/near/delta/5`) and `CompactWindowBlock`
(`PartIII-b:C/near/delta/8`, from `PartIIa.NearCompactFreeComparison`).

**Hypotheses left** (other-family statements): `PartIIa.NearStressMapExists`,
`IIIa.SepKernelBounds`, `IIIa.SepYoung`, `IIIa.PolyCausal`, `IIIa.FreeCausalExistsUnique`,
`PartI.TrainFluctuationDecay`, `PartI.TrainMeanExpansion`, `PartI.TrainMeanEquations`; and
`NearDeltaBoundC` (open `PartIII-b:C/near/delta`).
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **`near:masked-free-bound`** (source 4023-4031) from the other-family statements
`PartIIa.NearStressMapExists`, `IIIa.SepKernelBounds`, `IIIa.SepYoung` and the accepted leaves of
the masked branch. -/
theorem nearMaskedFreeBoundC_of_leaves (hN : UnforcedLeray.Short.PartIIa.NearStressMapExists)
    (hK : UnforcedLeray.Short.IIIa.SepKernelBounds) (hY : UnforcedLeray.Short.IIIa.SepYoung) :
    NearInst.NearMaskedFreeBoundC := by
  have hE : NearInst.Masked.RealStressBound :=
    NearInst.Masked.realStressBound_of hN
      (NearInst.Masked.stressMapUnique_of NearInst.Masked.tensorTestDense
        NearInst.Masked.tensorTestDivMem)
      (NearInst.Masked.stressTransportNorm_of (fun c hc => NearInst.Masked.cpcHT_eq c hc)
        (fun c hc => NearInst.Masked.cpcH_eq c hc))
  have hS : NearInst.Masked.MaskedSupport :=
    NearInst.Masked.maskedSupport_of NearInst.Masked.stressKernelRealization
      NearInst.Masked.boxDenseZ
  have hG : NearInst.Masked.GainBlockBound := NearInst.Masked.gainBlockBound
  exact NearInst.Masked.nearMaskedFreeBoundC_of
    (NearInst.Masked.maskedLowerPiece_of hE hS
      (NearInst.Masked.forbiddenBlockBound_of (NearInst.Masked.forbiddenKernelBound_of hK)
        NearInst.Masked.boxDenseZ) hG)
    (NearInst.Masked.maskedBinPiece_of hE (NearInst.Masked.farBlockZero_of NearInst.Masked.boxDenseZ)
      hS (NearInst.Masked.maskedStripBound_of NearInst.Masked.stressKernelRealization
        (NearInst.Masked.stripKernelBound_of hK hY) NearInst.Masked.boxDenseZ) hG)
    (NearInst.Masked.maskedUpperPiece_of hE
      (NearInst.Masked.farUpperZero_of NearInst.Masked.boxDenseZ) hG)
    NearInst.Masked.outBandPartition

/-- **`near:flat-bound`** (source 3881-3887, 3560-3581) from `IIIa.PolyCausal`,
`IIIa.FreeCausalExistsUnique` and the train statements of Part I (the actual train multiplier
bound, 2714-2729, 3566-3567). -/
theorem nearFlatBoundC_of_leaves (hPC : UnforcedLeray.Short.IIIa.PolyCausal)
    (hU : UnforcedLeray.Short.IIIa.FreeCausalExistsUnique)
    (hF : UnforcedLeray.Short.PartI.TrainFluctuationDecay)
    (hM : UnforcedLeray.Short.PartI.TrainMeanExpansion)
    (hE : UnforcedLeray.Short.PartI.TrainMeanEquations) : NearInst.NearFlatBoundC :=
  NearInst.nearFlatBoundC_of hPC (UnforcedLeray.Short.IIIa.polyStressCorollary_of_polyCausal hPC)
    hU (NearInst.flatTrainMultBound_of hF hM hE)

/-- **The near solver** (source 3943-3951, 4109-4124, 4023-4031) from the flat and masked
branches composed to their other-family inputs and `near:deltaN` (`NearDeltaBoundC`, open
`PartIII-b:C/near/delta`; composed in the task `PartIII-b:C/standing`). -/
theorem nearSolverC_of_layers (hD : NearInst.NearDeltaBoundC)
    (hN : UnforcedLeray.Short.PartIIa.NearStressMapExists)
    (hK : UnforcedLeray.Short.IIIa.SepKernelBounds) (hY : UnforcedLeray.Short.IIIa.SepYoung)
    (hPC : UnforcedLeray.Short.IIIa.PolyCausal)
    (hU : UnforcedLeray.Short.IIIa.FreeCausalExistsUnique)
    (hF : UnforcedLeray.Short.PartI.TrainFluctuationDecay)
    (hM : UnforcedLeray.Short.PartI.TrainMeanExpansion)
    (hE : UnforcedLeray.Short.PartI.TrainMeanEquations) : NearInst.NearSolverC :=
  NearInst.nearSolverC_of (nearFlatBoundC_of_leaves hPC hU hF hM hE) hD
    (nearMaskedFreeBoundC_of_leaves hN hK hY)

end UnforcedLeray.Short.PartIIIb.Concrete
