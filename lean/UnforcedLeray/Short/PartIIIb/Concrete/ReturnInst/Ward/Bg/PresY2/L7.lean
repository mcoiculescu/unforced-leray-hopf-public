import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_13_8_1.B3Bridge
import UnforcedLeray.Short.PartIIb.Tasks.HeatRemainder

/-!
# `PartIII-b:C/ward/13/7`: `BgUL4`

Source: `the November 2 reference manuscript` lines 2607-2610.
Assembles `bgUL4_proved` from `bgUL4_of_ballHeatRemainder` and
`UnforcedLeray.Short.IIb.ballHeatRemainder_proof`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem bgUL4_proved : BgUL4 := by
  exact bgUL4_of_ballHeatRemainder UnforcedLeray.Short.IIb.ballHeatRemainder_proof

end UnforcedLeray.Short.PartIIIb.Concrete
