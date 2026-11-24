import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.Bg.PresY2.Defs
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_13_8
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_13_8.L1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_13_8.L2

/-!
# `PartIII-b:C/ward/13/8`: `BgPresLeray`

Assembles `bgPresLeray_proved` from `bgPresLeray_of`, `bgDmuL2Sol_proved`, and
`bgPresGradClosure_proved`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem bgPresLeray_proved : BgPresLeray :=
  bgPresLeray_of bgDmuL2Sol_proved bgPresGradClosure_proved

end UnforcedLeray.Short.PartIIIb.Concrete
