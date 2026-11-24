import UnforcedLeray.Short.PartIIa.Sub.F03
import UnforcedLeray.Short.PartIIa.Tasks.F03aWindowEquation
import UnforcedLeray.Short.PartIIa.Tasks.F03bWindowNorms
import UnforcedLeray.Short.PartIIa.Tasks.F03cWindowBackEquation
import UnforcedLeray.Short.PartIIa.Tasks.F03dWindowBackNorm

/-!
# Part II-a, task `PartII-a:F03`: the fixed-window local graph estimate (unconditional)

Source of record: `the November 2 reference manuscript`, lines 1431-1441.
Assembles the four leaves (`F03/1` `windowEquation`, `F03/2` `windowNorms`, `F03/3`
`windowBackEquation`, `F03/4` `windowBackNorm`) into `localWindowEstimate_of` (`Sub/F03.lean`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIa

/-- **`PartII-a:F03`**: the fixed-window local graph estimate `LocalWindowEstimate`. -/
theorem localWindowEstimate : LocalWindowEstimate :=
  localWindowEstimate_of windowEquation windowNorms windowBackEquation windowBackNorm

end UnforcedLeray.Short.PartIIa
