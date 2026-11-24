import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T18_2_4_1_3_3
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence.NiceForceSolution.HeatCellClassical.DuhamelHeatEq.PhiDeriv.SpacePart
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence.NiceForceSolution.HeatCellClassical.DuhamelHeatEq.PhiDeriv.TimePart

/-!
# Part III-a, task `PartIII-a:T18/2/4/1/3/3`: `DuhEqPhiDeriv`

Target: `duhEqPhiDeriv : DuhEqPhiDeriv`, obtained from the space part `duhEqSpacePart`
(`PhiDeriv/SpacePart.lean`) and the time part `duhEqTimePart` (`PhiDeriv/TimePart.lean`) via
`duhEqPhiDeriv_of` (`Sub/PartIIIa_T18_2_4_1_3_3.lean`). Source: `the November 2 reference manuscript`,
lines 3427-3440.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIIa

theorem duhEqPhiDeriv : UnforcedLeray.Short.IIIa.DuhEqPhiDeriv :=
  duhEqPhiDeriv_of duhEqSpacePart duhEqTimePart

end UnforcedLeray.Short.IIIa

end
