import UnforcedLeray.Short.PartIIIa.Sub.T18_2_4_1
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence.NiceForceSolution.HeatCellClassical.DuhamelSmooth
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence.NiceForceSolution.HeatCellClassical.DuhamelPeriodicZero
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence.NiceForceSolution.HeatCellClassical.DuhamelHeatEq
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence.NiceForceSolution.HeatCellClassical.DuhamelDecay
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence.NiceForceSolution.HeatCellClassical.DivSourceNice
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence.NiceForceSolution.HeatCellClassical.CpowScale

/-!
# Part III-a, task `PartIII-a:T18/2/4/1`: `HeatCellClassical` from the six leaves

Target: `heatCellClassical : HeatCellClassical` (`Sub/T18_2_4.lean`).
Source of record: `the November 2 reference manuscript`, lines 3427-3440.

Proof: apply the conditional assembly `heatCellClassical_of` (`Sub/T18_2_4_1.lean`) to the six
leaf theorems `duhamelSmooth`, `duhamelPeriodicZero`, `duhamelHeatEq`, `duhamelDecay`,
`divSourceNice`, `cpowScale`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIIa

theorem heatCellClassical : UnforcedLeray.Short.IIIa.HeatCellClassical :=
  heatCellClassical_of duhamelSmooth duhamelPeriodicZero duhamelHeatEq duhamelDecay divSourceNice
    cpowScale

end UnforcedLeray.Short.IIIa

end
