import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_13_8_1.Org
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_13_8_1.BallRemainder
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_13_8_1.RemainderEvol
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.Bg.PresY2.L7

/-!
# `PartIII-b:C/ward/13/8/1/1`: `BgDmuMemL2`

Source: `the November 2 reference manuscript` lines 2584-2585, 2607-2635.
Assembles `bgDmuMemL2_proved` from `bgDmuMemL2_of_org`, `bgBallRemainder_proved`,
`bgRemainderEvol_proved`, `heatProfileDmuZero_proved`, and `bgUL4_proved`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem bgDmuMemL2_proved : BgDmuMemL2 := by
  exact bgDmuMemL2_of_org bgBallRemainder_proved bgRemainderEvol_proved
    heatProfileDmuZero_proved bgUL4_proved

end UnforcedLeray.Short.PartIIIb.Concrete
