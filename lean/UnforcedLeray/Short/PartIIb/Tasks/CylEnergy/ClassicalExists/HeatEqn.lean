import UnforcedLeray.Short.PartIIb.Sub.T22_1_8
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.HeatTimeDeriv
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.HeatLapTransfer
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.HeatCont

/-!


Assembles `HeatEqn` (`Sub/T22_1/Stages.lean`) from the two kernel-calculus leaves
`heatTimeDeriv` and `heatLapTransfer` and the proved `heatCont`, via `heatEqn_of`
(`Sub/T22_1_8.lean`). Source: `the November 2 reference manuscript`,
lines 2074-2093 and 2103-2105.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb.CylPDE

theorem heatEqn : UnforcedLeray.Short.IIb.CylPDE.HeatEqn :=
  heatEqn_of heatTimeDeriv HLT.heatLapTransfer heatCont

end UnforcedLeray.Short.IIb.CylPDE
