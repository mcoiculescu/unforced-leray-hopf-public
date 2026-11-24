import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_1
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations

/-!
# The mean stream is smooth for `s > 0` (source 397, `sct:mean`)

Proves `bgMeanSmooth` from the accepted Part I theorem `PartI.trainMeanEquations_proof`
(`TrainMeanEquations`, whose first conjunct is the joint smoothness of `S = meanStream` on
`{s > 0}`), applied to `p.train` with `p.ν > 0`, `p.c > 0` and `IsBUCTrain p.train`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **The mean stream is jointly smooth for `s > 0`** (source 397, `sct:mean`). -/
theorem bgMeanSmooth : BgMeanSmooth := by
  intro p d dm dp hreg
  exact (UnforcedLeray.Short.PartI.trainMeanEquations_proof p.ν p.c p.ν_pos p.c_pos p.train
    hreg.train_buc).1

end UnforcedLeray.Short.PartIIIb.Concrete
