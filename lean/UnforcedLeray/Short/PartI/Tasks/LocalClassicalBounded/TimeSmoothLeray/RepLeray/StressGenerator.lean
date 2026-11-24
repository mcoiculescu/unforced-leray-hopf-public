import UnforcedLeray.Short.PartI.Sub.T02_1_4_6_4
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.TimeSmoothLeray.RepLeray.StressGenerator.StressOrbitIsHeat
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.TimeSmoothLeray.RepLeray.StressGenerator.CenteredHeatAgeDerivative
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.TimeSmoothLeray.RepLeray.StressGenerator.CenteredHeatContinuity
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.TimeSmoothLeray.RepLeray.StressGenerator.DuhamelLeibnizL2
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.TimeSmoothLeray.RepLeray.StressGenerator.AdvectionL2Representative

/-!
# `stressGenerator`: the stress generator from the five leaves

Source of record: `the November 2 reference manuscript`, lines 261-288.
Task `PartI:T02/1/4/6/4` (assembly). Applies `stressGenerator_of` (`Sub/T02_1_4_6_4.lean`)
to the five leaf theorems.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartI

theorem stressGenerator : StressGenerator :=
  stressGenerator_of stressOrbitIsHeat centeredHeatAgeDerivative centeredHeatContinuity
    duhamelLeibnizL2 advectionL2Representative

end UnforcedLeray.Short.PartI
