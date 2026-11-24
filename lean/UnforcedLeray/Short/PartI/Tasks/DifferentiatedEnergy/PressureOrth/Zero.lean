import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.PressureOrth.Zero.IBP
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.PressureOrth.Zero.Tail
import UnforcedLeray.Short.PartI.Sub.PartI_T08_6_2

/-!


Source: `the November 2 reference manuscript`, line 346.
The proof is `jetPressureOrthZero_of` (in `Sub/PartI_T08_6_2.lean`) applied to the two leaves:
`etaCutIBP_proof` (`Zero/IBP.lean`) and `etaCutTail_proof` (`Zero/Tail.lean`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartI

theorem jetPressureOrthZero_proof : UnforcedLeray.Short.PartI.JetPressureOrthZero :=
  jetPressureOrthZero_of etaCutIBP_proof etaCutTail_proof

end UnforcedLeray.Short.PartI
