import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_7
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_6_2

/-!
# `n0cutLeN1` (PartIII-b:C/rep/7/3, source 4924-4927, 5400)

`oldN0cut` and `oldN0w` are the same integral (the cut old moment), so `N0cutLeN1` is
`N0wLeN1` (proved as `n0wLeN1` in `Sub/PartIII-b_C_rep_6_2.lean`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem n0cutLeN1 : UnforcedLeray.Short.PartIIIb.Concrete.N0cutLeN1 := by
  intro c ν χo hc hν hχ M hM
  exact n0wLeN1 c ν χo hc hν hχ M hM

end UnforcedLeray.Short.PartIIIb.Concrete
