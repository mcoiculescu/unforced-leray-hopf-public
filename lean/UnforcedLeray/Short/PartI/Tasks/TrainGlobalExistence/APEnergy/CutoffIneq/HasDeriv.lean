import UnforcedLeray.Short.PartI.Sub.PartI_T04_5_1_2
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APEnergy.CutoffIneq.DerivIntegral
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APEnergy.CutoffIneq.MomentumIdentity

/-!
# Part I, task `PartI:T04/5/1/2`: `APEnergyHasDeriv` from the derivative integral and the momentum identity

Source of record: `the November 2 reference manuscript`, lines 278-286.
Composition: `apEnergyHasDeriv_of` (`Sub/PartI_T04_5_1_2.lean`) applied to the leaves
`apEnergyDerivIntegral` (`PartI:T04/5/1/2/1`) and `apEnergyMomentumIdentity` (`PartI:T04/5/1/2/2`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory

namespace UnforcedLeray.Short.PartI

/-- `APEnergyHasDeriv` from the two leaves (`PartI:T04/5/1/2`). -/
theorem apEnergyHasDeriv : APEnergyHasDeriv :=
  apEnergyHasDeriv_of apEnergyDerivIntegral apEnergyMomentumIdentity

end UnforcedLeray.Short.PartI
