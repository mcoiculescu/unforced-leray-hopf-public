import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.TimeSmoothLeray.RepLeray.StressGenerator.StressOrbitIsHeat.N2
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.TimeSmoothLeray.RepLeray.StressGenerator.StressOrbitIsHeat.N3
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.TimeSmoothLeray.RepLeray.StressGenerator.StressOrbitIsHeat.N4
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.TimeSmoothLeray.RepLeray.StressGenerator.StressOrbitIsHeat.N5
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.TimeSmoothLeray.RepLeray.StressGenerator.StressOrbitIsHeat.Compose.KernelInputRowTensor
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.TimeSmoothLeray.RepLeray.StressGenerator.StressOrbitIsHeat.Compose.HeatVecAdvectionClass
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.TimeSmoothLeray.RepLeray.StressGenerator.StressOrbitIsHeat.RowTensorFDerivBound

/-!
# `heatDivStressIdentity`: the heat-divergence identity from the leaf facts

Source: `the November 2 reference manuscript`,
lines 261-288 (the Duhamel term of the mild solution is the heat flow of `div (u ⊗ u)`).

Applies `heatDivStressIdentity_of` (`Sub/T02_1_4_6_4_1/Compose.lean`) to the leaf theorems
`needRowDivHeat` (N2), `needRowTensorDivergence` (N3), `needHeatPeriodicL2` (N4),
`needZeroClassNormalized` (N5), `kernelInputRowTensor`, `heatVecAdvectionClass` and
`rowTensorFDerivBound`. Does not import `RowTensorDivergence.lean` (a second `rowDivergence`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartI

theorem heatDivStressIdentity : HeatDivStressIdentity :=
  heatDivStressIdentity_of needRowDivHeat needRowTensorDivergence needHeatPeriodicL2
    needZeroClassNormalized kernelInputRowTensor heatVecAdvectionClass rowTensorFDerivBound

end UnforcedLeray.Short.PartI
