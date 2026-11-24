import UnforcedLeray.Short.PartI.Sub.T02_1_4_6_4_1
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.TimeSmoothLeray.RepLeray.StressGenerator.HeatDivStressIdentity

/-!
# `stressOrbitIsHeat`: the stress orbit is the heat flow of the divergence

Source of record: `the November 2 reference manuscript`, lines 261-288.
Task `PartI:T02/1/4/6/4/1` (attempt 1): the heat-divergence identity
`heatDivStressIdentity` (task `PartI:T02/1/4/6/4/1/1`) feeds the reduction
`stressOrbitIsHeat_of` (`Sub/T02_1_4_6_4_1.lean`, line 50).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartI

theorem stressOrbitIsHeat : StressOrbitIsHeat :=
  stressOrbitIsHeat_of heatDivStressIdentity

end UnforcedLeray.Short.PartI
