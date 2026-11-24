import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_3_2_12_3
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Sub.IIIb_D2_3_2_12_3.Lin
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Sub.IIIb_D2_3_2_12_3.Bd
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Sub.IIIb_D2_3_2_12_3.Nonpos

/-!
# `PartIII-b:IIIb-D2/3/2/12/3` (`StrPairCont`): proved from the five facts

Source of record: `the November 2 reference manuscript`,
lines 2683, 2698-2700, 4284-4286.

Assembles `strPairCont_of` (statements in `PartIII-b_IIIb-D2_3_2_12_3.lean`) with the proved
facts `strPairLin_proved` (`Lin.lean`), `strPairBd_proved` (`Bd.lean`) and
`strPairContNonpos_proved` (`Nonpos.lean`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem strPairCont_proved (c mZ ρb γ ν ε : ℝ) : StrPairCont c mZ ρb γ ν ε :=
  strPairCont_of strPairLin_proved strPairBd_proved strPairContNonpos_proved c mZ ρb γ ν ε

end UnforcedLeray.Short.PartIIIb.Concrete
