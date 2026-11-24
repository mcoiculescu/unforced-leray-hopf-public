import UnforcedLeray.Short.PartI.Sub.PartI_T02_1_4_4_1_7_1_1_1_1_1
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.TimeSmoothLeray.MildPathTimeSmooth.MildPathDerivRhs.HeatGeneratorH5.GeneratorZero.Taylor.Remainder
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.TimeSmoothLeray.MildPathTimeSmooth.MildPathDerivRhs.HeatGeneratorH5.GeneratorZero.Taylor.GaussSplit
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.TimeSmoothLeray.MildPathTimeSmooth.MildPathDerivRhs.HeatGeneratorH5.GeneratorZero.Taylor.GaussCube

/-!
# Part I, `PartI:T02/1/4/4/1/7/1/1/1/1/1`: decomposition of `HeatTaylorUniform`

Source `the November 2 reference manuscript`, lines 261-288.  Assembles
`HeatTaylorUniform` from the three leaves `heatTaylorRemainder`, `heatGaussSplit`, `heatGaussCube`
via `heatTaylorUniform_of`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartI

/-- **Part I, `HeatTaylorUniform` (lines 261-288).** Assembly of the uniform second-order Taylor
bound from the pointwise remainder, the Gaussian split and the third absolute moment. -/
theorem heatTaylorUniform : HeatTaylorUniform :=
  heatTaylorUniform_of heatTaylorRemainder heatGaussSplit heatGaussCube

end UnforcedLeray.Short.PartI
