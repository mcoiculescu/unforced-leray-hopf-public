import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APLevel2.Integrated
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APLevel2.Static

/-!
# Part I, `PartI:T04/9`, target `apLevel2`: the first vorticity jet

Source of record: `the November 2 reference manuscript`, lines 285-288.
Closes `APLevel2` from the integrated leaf `apLevel2IntegratedW'` (`APLevel2/Integrated.lean`)
and the static leaf `apLevel2Static` (`APLevel2/Static.lean`) via `apLevel2_of`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartI

/-- `PartI:T04/9`: the first vorticity jet, conditional on no further leaves. -/
theorem apLevel2 : APLevel2 := apLevel2_of apLevel2IntegratedW' apLevel2Static

end UnforcedLeray.Short.PartI
