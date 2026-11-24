import UnforcedLeray.Short.PartIIa.ComposeRing
import UnforcedLeray.Short.PartIIa.Tasks.R01EarlyBound
import UnforcedLeray.Short.PartIIa.Tasks.R02LateTable
import UnforcedLeray.Short.PartIIa.Tasks.R05ResidualFromTable

/-!
# Part II-b, task `PartII-b:R1/1`: `ringResidualBound_proved`

Source of record: `the November 2 reference manuscript`, lines 1219-1225 and
1259-1297 (`sct:residual-bound`).

Combines `ringResidualBound_of_table` (`Short/PartII-a/ComposeRing.lean`) with `ringLateTable`
(`PartII-a:R02`), `ringEarlyBound` (`PartII-a:R01`) and `ringResidualFromTable` (`PartII-a:R05`).
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Short.PartIIa

theorem ringResidualBound_proved : UnforcedLeray.Short.PartIIa.RingResidualBound :=
  ringResidualBound_of_table ringLateTable ringEarlyBound ringResidualFromTable

end UnforcedLeray.Short.IIb
