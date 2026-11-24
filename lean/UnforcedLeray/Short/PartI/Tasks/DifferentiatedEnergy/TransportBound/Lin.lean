import UnforcedLeray.Short.PartI.Sub.PartI_T08_7_2
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.TransportBound.AdvInt
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.TransportBound.BoundA
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.TransportBound.BoundB

/-!
# Part I, task `PartI:T08/7/2` (`JTLin`): assembly

Source: `the November 2 reference manuscript` lines 352-358.
`JTLin` is assembled from the three leaves `JTAdvInt`, `JTBoundA`, `JTBoundB` by `jtLin_of`
(compiled in `Sub/PartI_T08_7_2.lean`).
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartI

theorem jtLin_proof : UnforcedLeray.Short.PartI.JTLin :=
  jtLin_of jtAdvInt_proof jtBoundA_proof jtBoundB_proof

end UnforcedLeray.Short.PartI
