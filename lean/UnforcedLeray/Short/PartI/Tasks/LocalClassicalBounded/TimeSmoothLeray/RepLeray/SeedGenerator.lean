import UnforcedLeray.Short.PartI.Sub.T02_1_4_6_3
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.TimeSmoothLeray.RepLeray.StressGenerator.CenteredHeatAgeDerivative

/-!
# Part I, task `PartI:T02/1/4/6/3`: the unconditional seed generator

Source of record: `the November 2 reference manuscript`, lines 261-288.

Target: `SeedGenerator` (`Short/PartI/Sub/T02_1_4_6.lean`).  The seed generator is the
conditional decomposition `seedGenerator_of` (`Short/PartI/Sub/T02_1_4_6_3.lean`) applied to the
unconditional leaf `centeredHeatAgeDerivative` (task `PartI:T02/1/4/6/4/2`, file
`Short/PartI/Tasks/LocalClassicalBounded/TimeSmoothLeray/RepLeray/StressGenerator/CenteredHeatAgeDerivative.lean`).
No `sorry`, `admit`, `axiom` or `native_decide`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartI

theorem seedGenerator : SeedGenerator :=
  seedGenerator_of centeredHeatAgeDerivative

end UnforcedLeray.Short.PartI
