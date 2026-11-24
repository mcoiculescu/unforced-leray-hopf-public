import UnforcedLeray.Short.PartIIa.Sub.N02_4_7_B
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.ModeBounds.J0
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.ModeBounds.J1

/-!
# Part II-a, task `PartII-a:N02/4/7`: the one-mode moment bound `NzModeBounds`

Source: `the November 2 reference manuscript`, lines 1722-1727.
The `j = 0` bound `nzmbJ0` (task `PartII-a:N02/4/7/8`) and the `j = 1` bound `nzmbJ1`
(task `PartII-a:N02/4/7/9`) are assembled into `NzModeBounds` by `nzModeBounds_of`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIa

theorem nzModeBounds : UnforcedLeray.Short.PartIIa.NzModeBounds :=
  nzModeBounds_of nzmbJ0 nzmbJ1

end UnforcedLeray.Short.PartIIa
