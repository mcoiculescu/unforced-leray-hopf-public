import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T16_2
import UnforcedLeray.Short.PartIIb.Tasks.HilbertBodyComparison.TestedGradientEnergy.SubtractedChartTestedEq
import UnforcedLeray.Short.PartIIb.Tasks.HilbertBodyComparison.TestedGradientEnergy.BoxDiffusionAbsorption

/-!
# `PartII-b:T16/2`: `TestedGradientEnergyH2`

Source: `the November 2 reference manuscript` lines 1955-1988.
Assembles `testedGradientEnergyH2_proof` from `testedGradientEnergyH2_of`,
`subtractedChartTestedEq_proof`, and `boxDiffusionAbsorption_proof`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

theorem testedGradientEnergyH2_proof : UnforcedLeray.Short.IIb.TestedGradientEnergyH2 :=
  testedGradientEnergyH2_of subtractedChartTestedEq_proof boxDiffusionAbsorption_proof

end UnforcedLeray.Short.IIb
