import UnforcedLeray.Short.PartI.Sub.T02_1_3
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.SpatialRepFromPersistent.CylSobolevRep
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.SpatialRepFromPersistent.AePeriodicEq

/-!
# Part I, task `PartI:T02/1/3`: `SpatialRepFromPersistent` (unconditional)

Source of record: `the November 2 reference manuscript`, lines 261-288.

Final assembly: the conditional theorem `spatialRepFromPersistent_of` (in `Sub/T02_1_3.lean`)
applied to the two leaf statements `cylSobolevRep` (task `PartI:T02/1/3/1`) and `aePeriodicEq`
(task `PartI:T02/1/3/2`).
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartI

/-- **Spatial smooth representative for positive time** (`SpatialRepFromPersistent`): the
unconditional statement, obtained from the conditional `spatialRepFromPersistent_of`. -/
theorem spatialRepFromPersistent : SpatialRepFromPersistent :=
  spatialRepFromPersistent_of cylSobolevRep aePeriodicEq

end UnforcedLeray.Short.PartI
