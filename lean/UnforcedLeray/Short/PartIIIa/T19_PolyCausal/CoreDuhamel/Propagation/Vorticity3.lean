import UnforcedLeray.Short.PartIIIa.T19_PolyCausal.CoreDuhamel.Propagation.Vorticity3.Leaves
import UnforcedLeray.Short.PartIIIa.T19_PolyCausal.CoreDuhamel.Propagation.Vorticity3.LeafA
import UnforcedLeray.Short.PartIIIa.T19_PolyCausal.CoreDuhamel.Propagation.Vorticity3.LeafB

/-!
# `PartIII-a:T19/2/3/2/3`: `CoreDuhamelFromClock`

Assembles `coreDuhamelFromClock` from `coreDuhamelFromClock_of`,
`coreDuhamelRep_proof`, and `coreSourceFinite_proof`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIIa

theorem coreDuhamelFromClock : UnforcedLeray.Short.IIIa.CoreDuhamelFromClock :=
  coreDuhamelFromClock_of coreDuhamelRep_proof coreSourceFinite_proof

end UnforcedLeray.Short.IIIa
