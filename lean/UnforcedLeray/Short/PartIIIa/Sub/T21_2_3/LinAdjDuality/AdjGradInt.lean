import UnforcedLeray.Short.PartIIIa.Sub.T21_2_2_1_F1.Reduction

/-!
# `PartIII-a:T21/2/3/1/1` (`ladAdjGradInt`)

`IsAdjointFlow` carries `strongContH1`, so `ρ ↦ ‖∂_kφ(ρ)‖_{X_{-m,c}}` is continuous on `[t, r]`
(SP 3060-3071). This is `ladAdjGradInt_direct` in `T21_2_2_1_F1/Reduction.lean`; the hypothesis
`8 < m` is not needed by that argument.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff Interval

namespace UnforcedLeray.Short.IIIa

theorem ladAdjGradInt (m : ℝ) (hm : 8 < m) : LadAdjGradInt m :=
  ladAdjGradInt_direct m

end UnforcedLeray.Short.IIIa
