import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.TranspApprox
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.TranspLimit
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_3_1_9_2

/-!
# `PartIII-a:T21/2/3/1/9` (`LadTransposition`): transposition from the two leaves

Uses `ladTranspApprox` (`TranspApprox.lean`, task `PartIII-a:T21/2/3/1/9/1`) and
`ladTranspLimitM` (`TranspLimit.lean`, task `PartIII-a:T21/2/3/1/9/2`), composed through
`ladTransposition_of_M` (`Sub/PartIII-a_T21_2_3_1_9_2.lean`).  The measurable-velocity version
`LadTranspLimitM` replaces `LadTranspLimit`, which is not provable as stated (see that file's
header).  Source: `the November 2 reference manuscript` (SP) lines 3052-3058.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.IIIa

theorem ladTransposition (m : ℝ) (hm : 8 < m) : LadTransposition m :=
  ladTransposition_of_M m hm (ladTranspApprox m hm) (ladTranspLimitM m hm)

end UnforcedLeray.Short.IIIa
