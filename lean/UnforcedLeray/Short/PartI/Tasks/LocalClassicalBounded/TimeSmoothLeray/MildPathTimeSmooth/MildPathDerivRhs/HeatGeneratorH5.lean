import UnforcedLeray.Short.PartI.Sub.PartI_T02_1_4_4_1_7
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.TimeSmoothLeray.MildPathTimeSmooth.MildPathDerivRhs.HeatGeneratorH5.SmoothGen
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.TimeSmoothLeray.MildPathTimeSmooth.MildPathDerivRhs.HeatGeneratorH5.DiffUniform

/-!
# Part I, task `PartI:T02/1/4/4/1/7`: the generator of the `H^3` heat semigroup on `H^5`

Source: `the November 2 reference manuscript`, lines 261-288.

`heatGeneratorH5_of_two (hSmooth : HeatSmoothGen5) (hBound : HeatDiffUniform5) : HeatGeneratorH5`.
The final task proves `theorem heatGeneratorH5 : HeatGeneratorH5` here from the two leaf
theorems `heatSmoothGen5 : HeatSmoothGen5` and `heatDiffUniform5 : HeatDiffUniform5`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartI

/-- **Part I, `HeatGeneratorH5` (lines 261-288).** The generator of the `H^3` heat semigroup on
`H^5`, from the two leaf theorems. -/
theorem heatGeneratorH5 : HeatGeneratorH5 :=
  heatGeneratorH5_of_two heatSmoothGen5 heatDiffUniform5

end UnforcedLeray.Short.PartI

end
