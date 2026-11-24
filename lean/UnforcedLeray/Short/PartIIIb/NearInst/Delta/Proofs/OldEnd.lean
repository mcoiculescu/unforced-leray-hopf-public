import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Sub.PartIIIb_C_near_delta_11
import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.FlatFreeGain
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.MaskedUpperPiece
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.RealStressBound
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.StressMapUnique
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.StressTransportNorm
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.FarUpperZero
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.GainBlockBound
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.TensorTestDense
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.TensorTestDivMem
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.CellPtHT
import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.OldEnd.CellPtHCopy
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.BoxDenseZ

/-!
# `oldEndResponse_of` (item `PartIII-b:C/near/delta/11`)

Source of record `the November 2 reference manuscript`,
4015-4020. Composition of `oldEndResponse_of_pieces` (the `S_N` piece and the flat free gain bound)
with the upper masked piece `maskedUpperPiece_of`, whose real stress bound, far-upper vanishing and
gain block bound are discharged by the compiled masked and flat lemmas.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Delta

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Cons.C03.Concrete
  UnforcedLeray.Blueprint.Planar

/-- The old end response, unconditional in the stress-map and free-solver hypotheses. -/
theorem oldEndResponse_of (hS : UnforcedLeray.Short.PartIIa.NearStressMapExists)
    (hU : UnforcedLeray.Short.IIIa.FreeCausalExistsUnique) : OldEndResponse :=
  oldEndResponse_of_pieces (flatFreeGainBound_of hU)
    (UnforcedLeray.Short.PartIIIb.NearInst.Masked.maskedUpperPiece_of
      (UnforcedLeray.Short.PartIIIb.NearInst.Masked.realStressBound_of hS
        (UnforcedLeray.Short.PartIIIb.NearInst.Masked.stressMapUnique_of
          UnforcedLeray.Short.PartIIIb.NearInst.Masked.tensorTestDense
          UnforcedLeray.Short.PartIIIb.NearInst.Masked.tensorTestDivMem)
        (UnforcedLeray.Short.PartIIIb.NearInst.Masked.stressTransportNorm_of
          UnforcedLeray.Short.PartIIIb.NearInst.Masked.cellPtHT_eq
          UnforcedLeray.Short.PartIIIb.NearInst.Masked.OldEndH.cellPtH_eq))
      (UnforcedLeray.Short.PartIIIb.NearInst.Masked.farUpperZero_of
        UnforcedLeray.Short.PartIIIb.NearInst.Masked.boxDenseZ)
      UnforcedLeray.Short.PartIIIb.NearInst.Masked.gainBlockBound)

end UnforcedLeray.Short.PartIIIb.NearInst.Delta
