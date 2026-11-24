import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_13_8_1.B3Bridge
import UnforcedLeray.Short.PartIIb.Tasks.HeatRemainder

/-!
# `PartIII-b:C/ward/13/8/1/1/org/1`: `BgBallRemainder`

Source: `the November 2 reference manuscript` lines 2505-2524, 2563-2633.
Assembles `bgBallRemainder_proved` from `bgBallRemainder_of_ballHeatRemainder` and
`UnforcedLeray.Short.IIb.ballHeatRemainder_proof`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem bgBallRemainder_proved : BgBallRemainder := by
  exact bgBallRemainder_of_ballHeatRemainder UnforcedLeray.Short.IIb.ballHeatRemainder_proof

end UnforcedLeray.Short.PartIIIb.Concrete
