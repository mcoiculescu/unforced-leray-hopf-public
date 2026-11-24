import UnforcedLeray.Short.PartI.Sub.PartI_T04_10_2
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APLevel3.SliceT1
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APLevel3.SliceT2

/-!
# Part I, `PartI:T04/10/2`: `APLevel3Static`

Source of record: `the November 2 reference manuscript`, lines 285-288.
Assembly: `apLevel3Static_of` closes `APLevel3Static` from the two slice-level leaves
`sliceT1Bound` (`PartI:T04/10/2/1`) and `sliceT2Bound` (`PartI:T04/10/2/2`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartI

/-- **Target `apLevel3Static`** (lines 285-288): `APLevel3Static` from the two slice-level
commutator leaves. -/
theorem apLevel3Static : APLevel3Static :=
  apLevel3Static_of sliceT1Bound sliceT2Bound

end UnforcedLeray.Short.PartI
