import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T19_2_3_2
import UnforcedLeray.Short.PartIIIa.T19_PolyCausal.CoreDuhamel.Propagation.Vorticity1
import UnforcedLeray.Short.PartIIIa.T19_PolyCausal.CoreDuhamel.Propagation.Vorticity2
import UnforcedLeray.Short.PartIIIa.T19_PolyCausal.CoreDuhamel.Propagation.Vorticity3

/-!
# `PartIII-a:T19/2/3/2`: `CoreDuhamelVorticityBound`

Assembles `coreDuhamelVorticityBound` from `coreDuhamelVorticityBound_of`,
`coreVortWeakEq`, `coreSourceNegBound`, and `coreDuhamelFromClock`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIIa

theorem coreDuhamelVorticityBound : UnforcedLeray.Short.IIIa.CoreDuhamelVorticityBound :=
  coreDuhamelVorticityBound_of coreVortWeakEq coreSourceNegBound coreDuhamelFromClock

end UnforcedLeray.Short.IIIa
