import UnforcedLeray.Short.PartIIa.Sub.F15
import UnforcedLeray.Short.PartIIa.Tasks.F15aWSUSolenoidal
import UnforcedLeray.Short.PartIIa.Tasks.F15bWSUWeakEq
import UnforcedLeray.Short.PartIIa.Tasks.F15cWSUPressure

/-!
# Part II-a, task `PartII-a:F15`: distributional uniqueness of the weak stress

Target: `weakStressUnique : WeakStressUnique` (`StatementsFree.lean`).

Assembly: `weakStressUnique_of` (Sub/F15) applied to
* `wsuSolenoidal` (F15/1, Tasks/F15aWSUSolenoidal);
* `wsuWeakEq` (F15/2, Tasks/F15bWSUWeakEq);
* `wsuPressure` (F15/3, Tasks/F15cWSUPressure).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIa

/-- **`PartII-a:F15`**: distributional uniqueness of the weak stress. -/
theorem weakStressUnique : WeakStressUnique :=
  weakStressUnique_of wsuSolenoidal wsuWeakEq wsuPressure

end UnforcedLeray.Short.PartIIa
