import UnforcedLeray.Short.PartI.Sub.PartI_T08_7
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.TransportBound.Split
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.TransportBound.Lin
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.TransportBound.Quad

/-!
# Part I, task `PartI:T08/7` (`JetTransportBound`): assembly

Source: `the November 2 reference manuscript` lines 352-358.
Assembled by `jetTransportBound_of` (compiled in `Sub/PartI_T08_7.lean`) from the leaves
`jetSplit_proof`, `jtLin_proof`, `jtQuad_proof`.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartI

theorem jetTransportBound_proof : UnforcedLeray.Short.PartI.JetTransportBound :=
  jetTransportBound_of jetSplit_proof jtLin_proof jtQuad_proof

end UnforcedLeray.Short.PartI
