import UnforcedLeray.Short.PartI.Sub.PartI_T02_1_4_4_1_7_1_1_1
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.TimeSmoothLeray.MildPathTimeSmooth.MildPathDerivRhs.HeatGeneratorH5.GeneratorZero

/-!
# Part I, `PartI:T02/1/4/4/1/7/1/1`: the `H^3` Duhamel identity from the age derivative

Source `the November 2 reference manuscript`, lines 261-288.

The viscosity-positive Duhamel identity `HeatDuhamelSmooth5` (with `0 < ν`) follows from the
age-derivative leaf `HeatAgeDerivSmooth5` (`heatDuhamelSmooth5_of`), which in turn follows from
the generator limit at age zero `HeatGeneratorAtZero5` (`heatAgeDerivSmooth5_of`), and that
generator limit is `heatGeneratorAtZero5`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartI

/-- **Part I, `HeatDuhamelSmooth5` (lines 261-288).** The `H^3` Duhamel identity for the heat
part of the cylinder mild solution, from the age-zero generator limit. -/
theorem heatDuhamelSmooth5 : HeatDuhamelSmooth5 :=
  heatDuhamelSmooth5_of (heatAgeDerivSmooth5_of heatGeneratorAtZero5)

end UnforcedLeray.Short.PartI

end
