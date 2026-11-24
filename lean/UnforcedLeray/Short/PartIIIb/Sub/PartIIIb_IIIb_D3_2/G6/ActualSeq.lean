import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G6.ActualSeq.Of
import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Proofs.TrainEvolutionExists
import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Proofs.BodyColumnFlat
import UnforcedLeray.Short.PartIIIa.T19_PolyCausal
import UnforcedLeray.Short.PartIIIa.T21_FullClock
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal
import UnforcedLeray.Short.PartIIIa.T05_HardyKernel

/-!
# `PartIII-b:IIIb-D3/2/G6/5`: the actual flat sequence and its column pin (`ActualSeqPinned`)

Source of record: `the November 2 reference manuscript` (73 pages):
lines 4349-4356, 4557-4618, 4650-4654, 4761-4763.

The conditional assembly `actualSeqPinned_of` and the seed-link normalization `seedLink_exists`
are proved and compiled in `G6/ActualSeq/Of.lean` and `G6/ActualSeq/SeedLink.lean`.
Task `PartIII-b:IIIb-D3/2/G6/5` states `theorem actualSeqPinned (D : SeqData) :
FlatUnif.G6.ActualSeqPinned D` here by applying `actualSeqPinned_of` to `trainEvolutionExists`,
`bodyColumnFlat`, and `polyCausal`.
-/

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G6

theorem actualSeqPinned (D : SeqData) : FlatUnif.G6.ActualSeqPinned D :=
  actualSeqPinned_of FlatSettingInst.trainEvolutionExists FlatSettingInst.bodyColumnFlat
    (IIIa.polyCausal IIIa.fullClockWeakForward IIIa.freeCausalExistsUnique IIIa.hardyKernel) D

end UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G6
