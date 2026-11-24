import UnforcedLeray.Short.PartI.Sub.PartI_T02_1_4_4_1_7_2
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.TimeSmoothLeray.MildPathTimeSmooth.MildPathDerivRhs.HeatGeneratorH5.Duhamel

/-!
# Part I, task `PartI:T02/1/4/4/1/7/2`: `HeatDiffUniform5` from the Duhamel leaf

Source `the November 2 reference manuscript`, lines 261-288.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartI

/-- **Part I, `HeatDiffUniform5` (lines 261-288).** The uniform difference-quotient bound, from the
Duhamel identity. -/
theorem heatDiffUniform5 : HeatDiffUniform5 :=
  heatDiffUniform5_of heatDuhamelSmooth5

end UnforcedLeray.Short.PartI

end
