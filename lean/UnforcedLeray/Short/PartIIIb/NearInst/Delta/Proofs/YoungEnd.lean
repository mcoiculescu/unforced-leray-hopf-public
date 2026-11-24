import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Sub.PartIIIb_C_near_delta_10
import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.YoungEnd.MaskedPiece
import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.FlatFreeGain
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.RealStressBound
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.StressMapUnique
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.TensorTestDense
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.TensorTestDivMem
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.StressTransportNorm
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.CellPtHT
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.CellPtH
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.MaskedSupport
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.StressKernelRealization
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.BoxDenseZ
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.ForbiddenBlockBound
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.ForbiddenKernelBound
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.GainBlockBound

/-!
# `youngEndResponse_of` (item `PartIII-b:C/near/delta/10`)

Source of record `the November 2 reference manuscript`, 4011-4015.
Assembly of `youngEndResponse_of_pieces` (Sub file `PartIII-b_C_near_delta_10`) from the flat
free gain bound `flatFreeGainBound_of` (delta/7) and the young masked piece `youngMaskedPiece_of`
(delta/10/1), whose hypotheses are supplied by the masked leaves. The separated hypothesis `hY`
is not needed for this end.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.NearInst.Delta

theorem youngEndResponse_of (hS : UnforcedLeray.Short.PartIIa.NearStressMapExists)
    (hK : UnforcedLeray.Short.IIIa.SepKernelBounds) (hY : UnforcedLeray.Short.IIIa.SepYoung)
    (hU : UnforcedLeray.Short.IIIa.FreeCausalExistsUnique) : YoungEndResponse :=
  youngEndResponse_of_pieces (flatFreeGainBound_of hU)
    (youngMaskedPiece_of
      (UnforcedLeray.Short.PartIIIb.NearInst.Masked.realStressBound_of hS
        (UnforcedLeray.Short.PartIIIb.NearInst.Masked.stressMapUnique_of
          UnforcedLeray.Short.PartIIIb.NearInst.Masked.tensorTestDense
          UnforcedLeray.Short.PartIIIb.NearInst.Masked.tensorTestDivMem)
        (UnforcedLeray.Short.PartIIIb.NearInst.Masked.stressTransportNorm_of
          UnforcedLeray.Short.PartIIIb.NearInst.Masked.cellPtHT_eq
          UnforcedLeray.Short.PartIIIb.NearInst.Masked.cellPtH_eq))
      (UnforcedLeray.Short.PartIIIb.NearInst.Masked.maskedSupport_of
        UnforcedLeray.Short.PartIIIb.NearInst.Masked.stressKernelRealization
        UnforcedLeray.Short.PartIIIb.NearInst.Masked.boxDenseZ)
      (UnforcedLeray.Short.PartIIIb.NearInst.Masked.forbiddenBlockBound_of
        (UnforcedLeray.Short.PartIIIb.NearInst.Masked.forbiddenKernelBound_of hK)
        UnforcedLeray.Short.PartIIIb.NearInst.Masked.boxDenseZ)
      UnforcedLeray.Short.PartIIIb.NearInst.Masked.gainBlockBound)

end UnforcedLeray.Short.PartIIIb.NearInst.Delta
