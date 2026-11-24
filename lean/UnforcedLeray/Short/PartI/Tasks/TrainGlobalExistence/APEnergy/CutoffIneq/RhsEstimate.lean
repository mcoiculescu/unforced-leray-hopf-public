import UnforcedLeray.Short.PartI.Sub.PartI_T04_5_1_3
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APEnergy.CutoffIneq.DissipationSign
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APEnergy.CutoffIneq.CrossEstimate
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APEnergy.CutoffIneq.TransportEstimate
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APEnergy.CutoffIneq.PressureEstimate

/-!
# Part I, task `PartI:T04/5/1/3`: `APEnergyRhsEstimate` from four term estimates

Source of record: `the November 2 reference manuscript`, lines 278-286.
Composition: `apEnergyRhsEstimate_of` (`Sub/PartI_T04_5_1_3.lean`) applied to the leaves
`apEnergyDissipationSign`, `apEnergyCrossEstimate`, `apEnergyTransportEstimate`,
`apEnergyPressureEstimate` (`PartI:T04/5/1/3/1` to `/3/4`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory

namespace UnforcedLeray.Short.PartI

/-- `APEnergyRhsEstimate` from the four leaves (`PartI:T04/5/1/3`). -/
theorem apEnergyRhsEstimate : APEnergyRhsEstimate :=
  apEnergyRhsEstimate_of apEnergyDissipationSign apEnergyCrossEstimate
    apEnergyTransportEstimate apEnergyPressureEstimate

end UnforcedLeray.Short.PartI
