import UnforcedLeray.Short.PartI.Sub.PartI_T04_10
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APLevel3.Integrated
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APLevel3.Static
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APLevel3.Gronwall

/-!
# Part I, `PartI:T04/10`, target `apLevel3`: the second vorticity jet

Source of record: `the November 2 reference manuscript`, lines 285-288.
Closes `APLevel3` from the three leaves `apLevel3Integrated` (`APLevel3/Integrated.lean`),
`apLevel3Static` (`APLevel3/Static.lean`) and `integralGronwall` (`APLevel3/Gronwall.lean`)
via `apLevel3_of` (`Sub/PartI_T04_10.lean`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartI

/-- `PartI:T04/10`: the second vorticity jet, conditional on no further leaves. -/
theorem apLevel3 : APLevel3 :=
  apLevel3_of apLevel3Integrated apLevel3Static integralGronwall

end UnforcedLeray.Short.PartI
