import UnforcedLeray.Short.PartIIa.Sub.F14
import UnforcedLeray.Short.PartIIa.Tasks.F14SmoothStressMap
import UnforcedLeray.Short.PartIIa.Tasks.F12aSmoothSymSubmodule
import UnforcedLeray.Short.PartIIa.Tasks.F12TensorDensity

/-!
# Part II-a, task `PartII-a:F14`: the weak stress extension exists

Target: `weakStressExists : WeakStressExists` (`StatementsFree.lean`).

Assembly: `weakStressExists_of` (Sub/F14) applied to
* `smoothStressMap` (F14/1, Tasks/F14SmoothStressMap);
* `smoothSymSubmodule` (F12a, Tasks/F12aSmoothSymSubmodule);
* `smoothTensorsDense` (F12, Tasks/F12TensorDensity).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIa

/-- **`PartII-a:F14`**: the weak stress extension exists. -/
theorem weakStressExists : WeakStressExists :=
  weakStressExists_of smoothStressMap smoothSymSubmodule smoothTensorsDense

end UnforcedLeray.Short.PartIIa
