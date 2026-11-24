import UnforcedLeray.Short.PartI.Sub.PartI_T02_1_4_4_1_7_1
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.TimeSmoothLeray.MildPathTimeSmooth.MildPathDerivRhs.HeatGeneratorH5.Duhamel
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.TimeSmoothLeray.MildPathTimeSmooth.MildPathDerivRhs.HeatGeneratorH5.LapIdentify

/-!
# Part I, task `PartI:T02/1/4/4/1/7/1`: `HeatSmoothGen5` from the Duhamel and Laplacian leaves

Source `the November 2 reference manuscript`, lines 261-288.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartI

/-- **Part I, `HeatSmoothGen5` (lines 261-288).** The generator limit on smooth fields, from the
Duhamel identity and the Laplacian identification leaves. -/
theorem heatSmoothGen5 : HeatSmoothGen5 :=
  heatSmoothGen5_of heatDuhamelSmooth5 heatLapSmoothIdentify5

end UnforcedLeray.Short.PartI

end
