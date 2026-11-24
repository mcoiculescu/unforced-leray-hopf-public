import UnforcedLeray.Short.PartI.Sub.PartI_T04_5
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APEnergy.CutoffIneq

/-!
# Part I, task `PartI:T04/5`: the velocity energy inequality

Source of record: `the November 2 reference manuscript`, lines 278-287.
Composition: `apEnergy_of` (`Sub/PartI_T04_5.lean`) applied to the cutoff inequality
`apEnergyCutoffIneq` (`Tasks/TrainGlobalExistence/APEnergy/CutoffIneq.lean`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartI

/-- `PartI:T04/5`: the velocity energy inequality `‖v(s)‖₂ ≤ ‖v(0)‖₂`. -/
theorem apEnergy : APEnergy := apEnergy_of apEnergyCutoffIneq

end UnforcedLeray.Short.PartI
