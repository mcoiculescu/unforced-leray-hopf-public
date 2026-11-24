import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_13_8_1.B3Bridge
import UnforcedLeray.Short.PartIIb.Tasks.HeatRemainder

/-!
# `PartIII-b:C/ward/13/8/1/1/org/2`: `BgRemainderEvol`

Source: `the November 2 reference manuscript` lines 2610-2632, 4140-4141.
Assembles `bgRemainderEvol_proved` from `bgRemainderEvol_of_ballHeatRemainder` and
`UnforcedLeray.Short.IIb.ballHeatRemainder_proof`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem bgRemainderEvol_proved : BgRemainderEvol := by
  exact bgRemainderEvol_of_ballHeatRemainder UnforcedLeray.Short.IIb.ballHeatRemainder_proof

end UnforcedLeray.Short.PartIIIb.Concrete
