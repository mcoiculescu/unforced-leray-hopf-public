import UnforcedLeray.Short.PartI.Sub.PartI_T02_1_4_4_1_7_1_1_1_1
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.TimeSmoothLeray.MildPathTimeSmooth.MildPathDerivRhs.HeatGeneratorH5.GeneratorZero.DerivQuot

/-!
# Part I, `PartI:T02/1/4/4/1/7/1/1/1/1`: the `H^3` generator at age zero

Source `the November 2 reference manuscript`, lines 261-288.

The open leaf `HeatGeneratorAtZero5` follows from the `H^3`-derivative form of the generator
limit `HeatH3DerivQuot`, proved in `GeneratorZero/DerivQuot.lean` (task `/1/3`), via the
componentwise reduction `heatGeneratorAtZero5_of`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartI

/-- **Part I, `HeatGeneratorAtZero5` (lines 261-288).** The generator limit at age zero in `H^3`,
from the componentwise `H^3` derivative limits `heatH3DerivQuot`. -/
theorem heatGeneratorAtZero5 : HeatGeneratorAtZero5 :=
  heatGeneratorAtZero5_of heatH3DerivQuot

end UnforcedLeray.Short.PartI
