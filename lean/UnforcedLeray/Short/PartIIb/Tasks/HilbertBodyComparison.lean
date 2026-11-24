import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T16
import UnforcedLeray.Short.PartIIb.Tasks.HilbertBodyComparison.CompactFreeBodyRate
import UnforcedLeray.Short.PartIIb.Tasks.HilbertBodyComparison.TestedGradientEnergy

/-!
# Part II-b, task `PartII-b:T16` (`HilbertBodyComparison`)

Source of record: `the November 2 reference manuscript`, lines 1955-1990
(Hilbert endpoint of `bg:lp-free-comparison`, `CompRate 2 (1/4) (1/28)`).

Definitions (`indBox`, `CompactFreeBodyRateH2`, `TestedGradientEnergyH2`) and the conditional
assembly `hilbertBodyComparison_of` live in `Short/PartII-b/Sub/PartII-b_T16.lean`.
Once the leaves `PartII-b:T16/1` (`compactFreeBodyRateH2_proof`) and `PartII-b:T16/2`
(`testedGradientEnergyH2_proof`) are proved, assemble
`hilbertBodyComparison_proof : HilbertBodyComparison` here.
-/

namespace UnforcedLeray.Short.IIb

theorem hilbertBodyComparison_proof : HilbertBodyComparison :=
  hilbertBodyComparison_of compactFreeBodyRateH2_proof testedGradientEnergyH2_proof

end UnforcedLeray.Short.IIb
