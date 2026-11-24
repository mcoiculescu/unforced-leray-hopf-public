import UnforcedLeray.Short.PartI.Sub.PartI_T04_10_2_2
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APLevel3.SliceT2.D2OmegaCube
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APLevel3.SliceT2.DuSup
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APLevel3.SliceT2.Holder333

/-!
# Part I, `PartI:T04/10/2/2`: `sliceT2Bound`, the second slice-level commutator leaf

Source of record: `the November 2 reference manuscript`, lines 285-288
(`t2 = |D²ω|² |Dv|`). Assembly of `sliceT2Bound_of` from `sliceD2OmegaCube`, `sliceDuSup`
and `holder333`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartI

/-- **Target `sliceT2Bound`** (lines 285-288): `SliceT2Bound` from the three source facts. -/
theorem sliceT2Bound : SliceT2Bound :=
  sliceT2Bound_of sliceD2OmegaCube sliceDuSup holder333

end UnforcedLeray.Short.PartI
