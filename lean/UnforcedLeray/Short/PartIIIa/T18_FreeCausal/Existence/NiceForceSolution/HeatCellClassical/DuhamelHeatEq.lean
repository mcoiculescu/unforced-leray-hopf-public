import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T18_2_4_1_3
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence.NiceForceSolution.HeatCellClassical.DuhamelHeatEq.Dt
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence.NiceForceSolution.HeatCellClassical.DuhamelHeatEq.Lap
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence.NiceForceSolution.HeatCellClassical.DuhamelHeatEq.PhiDeriv
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence.NiceForceSolution.HeatCellClassical.DuhamelHeatEq.ApproxId
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence.NiceForceSolution.HeatCellClassical.DuhamelHeatEq.FTC

/-!
# Part III-a, task `PartIII-a:T18/2/4/1/3`: `DuhamelHeatEq` from the five leaves

Target: `duhamelHeatEq : DuhamelHeatEq` (`Sub/T18_2_4_1.lean`, `Sub/PartIIIa_T18_2_4_1_3.lean`).
Source of record: `the November 2 reference manuscript`, lines 3427-3440.

Proof: apply `duhamelHeatEq_of` to the five leaf theorems `duhEqDt`, `duhEqLap`, `duhEqPhiDeriv`,
`duhEqApproxId`, `duhEqFTC`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIIa

theorem duhamelHeatEq : UnforcedLeray.Short.IIIa.DuhamelHeatEq :=
  duhamelHeatEq_of duhEqDt duhEqLap duhEqPhiDeriv duhEqApproxId duhEqFTC

end UnforcedLeray.Short.IIIa

end
