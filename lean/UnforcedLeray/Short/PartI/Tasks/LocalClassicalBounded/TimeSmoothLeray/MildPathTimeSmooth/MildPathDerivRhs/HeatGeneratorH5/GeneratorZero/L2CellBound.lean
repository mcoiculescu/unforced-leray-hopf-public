import UnforcedLeray.Short.PartI.Sub.PartI_T02_1_4_4_1_7_1_1_1_1_2_1
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.TimeSmoothLeray.MildPathTimeSmooth.MildPathDerivRhs.HeatGeneratorH5.GeneratorZero.L2CellBound.TailConv
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.TimeSmoothLeray.MildPathTimeSmooth.MildPathDerivRhs.HeatGeneratorH5.GeneratorZero.L2CellBound.TailElem
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.TimeSmoothLeray.MildPathTimeSmooth.MildPathDerivRhs.HeatGeneratorH5.GeneratorZero.L2CellBound.GaussCellL2
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.TimeSmoothLeray.MildPathTimeSmooth.MildPathDerivRhs.HeatGeneratorH5.GeneratorZero.L2CellBound.CylSmoothBdd

/-!
# Part I, `PartI:T02/1/4/4/1/7/1/1/1/1/2/1`: `HeatCellL2Bound`

Source `the November 2 reference manuscript`, lines 261-288.

Assembly of the four leaves (`HeatTailConv`, `HeatTailElem`, `GaussCellL2`, `CylSmoothBdd`)
into `HeatCellL2Bound` via `heatCellL2Bound_of`.
-/

set_option autoImplicit false

noncomputable section

/-- **`HeatCellL2Bound`, assembled from the four leaves (source lines 261-288).** -/
theorem heatCellL2Bound : UnforcedLeray.Short.PartI.HeatCellL2Bound :=
  UnforcedLeray.Short.PartI.heatCellL2Bound_of heatTailConv heatTailElem gaussCellL2 cylSmoothBdd
