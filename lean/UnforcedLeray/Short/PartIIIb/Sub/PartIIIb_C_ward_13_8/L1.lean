import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_13_8_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_13_8_1.L1

/-!
# `PartIII-b:C/ward/13/8/1`: `BgDmuL2Sol`

Assembles `bgDmuL2Sol_proved` from `bgDmuL2Sol_of` and `bgDmuMemL2_proved`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem bgDmuL2Sol_proved : BgDmuL2Sol := by
  exact bgDmuL2Sol_of bgDmuMemL2_proved

end UnforcedLeray.Short.PartIIIb.Concrete
