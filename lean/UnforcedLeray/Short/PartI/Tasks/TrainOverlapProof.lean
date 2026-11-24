import UnforcedLeray.Short.PartI.Sub.OverlapAndTailsDesign
import UnforcedLeray.Short.PartI.Tasks.TrainMeanEquations

/-!
# Part I, Task T16: Conditional proof of `TrainOverlap`

Source of record: `the November 2 reference manuscript`, lines 304-313, 389-425.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartI

/-- **Overlap decay (`PartI:T16`)** (source lines 304-313, 389-425):
assembles `TrainOverlap` from `trainMeanEquations_proof` (`PartI:T01`),
`OverlapFluctuationDecay` (`PartI:T13`), and `OverlapMeanDecay` (`PartI:T15`). -/
theorem trainOverlap_proof (hFD : OverlapFluctuationDecay) (hMD : OverlapMeanDecay) : TrainOverlap :=
  trainOverlap_of trainMeanEquations_proof hFD hMD

end UnforcedLeray.Short.PartI
