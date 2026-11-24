import UnforcedLeray.Short.PartI.Sub.PartI_T08_7_2_3
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.TransportBound.BoundB.Expand
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.TransportBound.BoundB.Term
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.TransportBound.BoundB.Count

/-!
# Part I, task `PartI:T08/7/2/3` (`JTBoundB`): assembly

Source: `the November 2 reference manuscript` lines 352-358 (differentiated
transport, `‖[D^j, e·∇]e‖₂ ≤ C_j ‖∇e‖_∞ ‖D^j e‖₂`).

The leaves are proved in `TransportBound/BoundB/Expand.lean` (`jtExpand_proof`),
`TransportBound/BoundB/Term.lean` (`jtBTerm_proof`) and `TransportBound/BoundB/Count.lean`
(`jtBCount_proof`). The assembly `jtBoundB_of` is in `Sub/PartI_T08_7_2_3.lean`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartI

theorem jtBoundB_proof : UnforcedLeray.Short.PartI.JTBoundB :=
  jtBoundB_of jtExpand_proof jtBTerm_proof jtBCount_proof

end UnforcedLeray.Short.PartI
