import UnforcedLeray.Short.PartI.Sub.PartI_T04_5
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APEnstrophy.CutoffIneq

/-!
# Part I, task `PartI:T04/6`: the vorticity energy inequality

Source of record: `the November 2 reference manuscript`, lines 285-287.
Composition: `apEnstrophy_of` (`Sub/PartI_T04_5.lean`) applied to the cutoff inequality
`apEnstrophyCutoffIneq` (`Tasks/TrainGlobalExistence/APEnstrophy/CutoffIneq.lean`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartI

/-- `PartI:T04/6`: the vorticity energy inequality `‖ω(s)‖₂ ≤ ‖ω(0)‖₂`. -/
theorem apEnstrophy : APEnstrophy := apEnstrophy_of apEnstrophyCutoffIneq

end UnforcedLeray.Short.PartI
