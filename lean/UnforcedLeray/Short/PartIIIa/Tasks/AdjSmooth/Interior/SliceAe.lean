import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_1_1_9
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.SliceAe.PeriodicBoxBound
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.SliceAe.AeDense
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.SliceAe.AeAllBoxes
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.SliceAe.BoxSliceTendsto

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIIa

/-- `PartIII-a:T21/2/7/2/1/1/9`: slices of a continuous version (`STRepSliceAe`). -/
theorem stRepSliceAe : STRepSliceAe :=
  stRepSliceAe_of periodicBoxBound aeDense aeAllBoxes boxSliceTendsto

end UnforcedLeray.Short.IIIa
