import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_3_1_9_2

/-!
# `PartIII-a:T21/2/3/1/9/2` target: `ladTranspLimitM`

Source: `the November 2 reference manuscript` (SP) lines 3052-3058.

`LadTranspLimitM m` (defined in `PartIII-a_T21_2_3_1_9_2.lean`) is `LadTranspLimit` with the
a.e. measurability of the approximating velocities added. Its proof `ladTranspLimitM_aux`
holds for every real `m`, so the hypothesis `8 < m` is not used.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIIa

theorem ladTranspLimitM (m : ℝ) (hm : 8 < m) : LadTranspLimitM m :=
  ladTranspLimitM_aux m

end UnforcedLeray.Short.IIIa
