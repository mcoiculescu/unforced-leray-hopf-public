import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.Bg.YoungW2.Defs
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_1.Fluct
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_1.Mean
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_1.MeanSmooth
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_1.Mixed
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_1.MeanSlice

/-!
# `bgTrainStreamYoungJets_of`: weighted young-band jets of the train stream

Source of record: `the November 2 reference manuscript`, lines 439-459 and 5461-5464.

The proof assembles the five parts of the decomposition `Ψ = (ψ - S) + S` in
`Sub/PartIII-b_C_ward_12_1.lean` (`bgTrainStreamYoungJets_of_parts`) with the proved
pieces `bgFluctWeighted_of`, `bgMeanWeighted_of`, `bgMeanSmooth`, `mixedToFull`, `meanSliceJet`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem bgTrainStreamYoungJets_of (hF : UnforcedLeray.Short.PartI.TrainFluctuationDecay)
    (hM : UnforcedLeray.Short.PartI.TrainMeanExpansion) : BgTrainStreamYoungJets :=
  bgTrainStreamYoungJets_of_parts (bgFluctWeighted_of hF) (bgMeanWeighted_of hM) bgMeanSmooth
    mixedToFull meanSliceJet

end UnforcedLeray.Short.PartIIIb.Concrete
