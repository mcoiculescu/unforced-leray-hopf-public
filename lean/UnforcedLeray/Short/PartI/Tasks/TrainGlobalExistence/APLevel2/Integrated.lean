import UnforcedLeray.Short.PartI.Sub.PartI_T04_9_1
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APLevel2.CutCont
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APLevel2.CutIneq
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APLevel2.Integ

/-!
# Part I, `PartI:T04/9/1`: `APLevel2IntegratedW`, assembled from the three leaves

Source of record: `the November 2 reference manuscript`, lines 285-288.

The leaves `apLevel2CutCont` (`PartI:T04/9/1/1`), `apLevel2CutIneq` (`PartI:T04/9/1/2`) and
`apLevel2Integ` (`PartI:T04/9/1/3`) are fed to `apLevel2IntegratedW_of` (`Sub/PartI_T04_9_1.lean`),
which carries out the limit `R → ∞` and returns the integrated inequality for the operator-norm
jets with the constants `2, 4`.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartI

/-- `PartI:T04/9/1`: the integrated first-jet inequality `APLevel2IntegratedW`, from the three
leaves. -/
theorem apLevel2IntegratedW' : APLevel2IntegratedW :=
  apLevel2IntegratedW_of apLevel2CutCont apLevel2CutIneq apLevel2Integ

end UnforcedLeray.Short.PartI
