import UnforcedLeray.Short.PartI.Sub.PartI_T04_5_1
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APEnergy.CutoffIneq.Continuous
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APEnergy.CutoffIneq.HasDeriv
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APEnergy.CutoffIneq.RhsEstimate

/-!
# Part I, task `PartI:T04/5/1`: `APEnergyCutoffIneq` from the three leaves

Source of record: `the November 2 reference manuscript`, lines 278-286.
Composition: `apEnergyCutoffIneq_of` (`Sub/PartI_T04_5_1.lean`) applied to the leaves
`apEnergyContinuous` (`PartI:T04/5/1/1`), `apEnergyHasDeriv` (`PartI:T04/5/1/2`) and
`apEnergyRhsEstimate` (`PartI:T04/5/1/3`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory

namespace UnforcedLeray.Short.PartI

/-- `APEnergyCutoffIneq` from the three leaves (`PartI:T04/5/1`). -/
theorem apEnergyCutoffIneq : APEnergyCutoffIneq :=
  apEnergyCutoffIneq_of apEnergyContinuous apEnergyHasDeriv apEnergyRhsEstimate

end UnforcedLeray.Short.PartI
