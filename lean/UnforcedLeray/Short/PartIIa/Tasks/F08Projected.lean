import UnforcedLeray.Short.PartIIa.Sub.F08
import UnforcedLeray.Short.PartIIa.Tasks.F08cLerayYResolventComm

/-!
# Part II-a, task `PartII-a:F08`: the projected inverse exists and is solenoidal

Source `the November 2 reference manuscript` lines 1358-1359 and 1498-1500.
Target: `commonBodyProjected : CommonBodyProjected` (`StatementsFree.lean`).

Assembly: `commonBodyProjected_of` (Sub/F08) applied to the leaf `lerayYResolventComm_proof`
(F08/3, Tasks/F08cLerayYResolventComm).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIa

/-- **`PartII-a:F08`**: the projected inverse `(μ+L)w = 𝐏f` exists and is solenoidal. -/
theorem commonBodyProjected : CommonBodyProjected :=
  commonBodyProjected_of lerayYResolventComm_proof

end UnforcedLeray.Short.PartIIa
