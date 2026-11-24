import UnforcedLeray.Short.PartI.Sub.PartI_T02_1_4_4_1_7_1_1_1_1_2
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.TimeSmoothLeray.MildPathTimeSmooth.MildPathDerivRhs.HeatGeneratorH5.GeneratorZero.L2CellBound

/-!
# Part I, `PartI:T02/1/4/4/1/7/1/1/1/1/2`: `HeatL2GeneratorSmooth`

Source `the November 2 reference manuscript`, lines 261-288.

`HeatL2GeneratorSmooth` follows from the `L^2(cell)` Taylor bound `heatCellL2Bound`
via `heatL2GeneratorSmooth_of`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartI

/-- **Part I, `HeatL2GeneratorSmooth` (lines 261-288).** The `L^2(cell)` generator limit for
cylinder-smooth fields, from the `L^2(cell)` Taylor bound. -/
theorem heatL2GeneratorSmooth : HeatL2GeneratorSmooth :=
  heatL2GeneratorSmooth_of heatCellL2Bound

end UnforcedLeray.Short.PartI
