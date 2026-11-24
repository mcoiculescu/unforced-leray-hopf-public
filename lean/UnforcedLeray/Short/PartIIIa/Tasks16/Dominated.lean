import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T16_1
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T16_1_1

/-!
# Part III-a, `PartIII-a:T16/1`: `SepWDominated` (SP 3604-3623)

`sepWDominated` is `sepWDominated_of` applied to the proved differentiation-under-the-integral
statement `sepWDiffUnder_proved` (task `PartIII-a:T16/1/1`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIIa

theorem sepWDominated : UnforcedLeray.Short.IIIa.SepWDominated :=
  sepWDominated_of sepWDiffUnder_proved

end UnforcedLeray.Short.IIIa

end
