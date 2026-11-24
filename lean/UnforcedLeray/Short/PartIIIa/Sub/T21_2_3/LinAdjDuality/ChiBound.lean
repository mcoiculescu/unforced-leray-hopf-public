import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.AdjWeakChi
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.AdjWeakSmooth

/-!
# Part III-a, task `PartIII-a:T21/2/3/1/8` (`ladChiBound`)

Source of record: `the November 2 reference manuscript` (SP) lines 3052-3058.
The bound `LadChiBound m` for `IsAdjointFlow` follows from the bound for jointly smooth weak
solutions (`adjWeakChiBound`) via `ladChiBound_of_weak`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIIa

theorem ladChiBound (m : ℝ) (hm : 8 < m) : LadChiBound m :=
  ladChiBound_of_weak m (adjWeakChiBound m hm)

end UnforcedLeray.Short.IIIa
