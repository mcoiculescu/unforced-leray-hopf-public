import UnforcedLeray.Short.PartI.Sub.PartI_T02_1_4_6_4_1_1_6_Bridges
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.TimeSmoothLeray.RepLeray.StressGenerator.StressOrbitIsHeat.Compose.CenteredVecTransportPeriodicAE
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.TimeSmoothLeray.RepLeray.StressGenerator.StressOrbitIsHeat.Compose.AdvectionPeriodicContinuous
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.TimeSmoothLeray.RepLeray.StressGenerator.StressOrbitIsHeat.Compose.HeatVecOfPeriodicClass

/-!
# Sub3: `HeatVecAdvectionClass`

Proves `HeatVecAdvectionClass` (Sub file, Sub3; source lines 261-288 of
`the November 2 reference manuscript`) from `heatVecAdvectionClass_of`
(Bridges file) applied to the leaf theorems `centeredVecTransportPeriodicAE` (Bridge 3a),
`advectionPeriodicContinuous` (Bridge 3b) and `heatVecOfPeriodicClass` (Bridge 3c).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartI

theorem heatVecAdvectionClass : HeatVecAdvectionClass :=
  heatVecAdvectionClass_of centeredVecTransportPeriodicAE advectionPeriodicContinuous
    heatVecOfPeriodicClass

end UnforcedLeray.Short.PartI
