import UnforcedLeray.Short.PartI.Sub.PartI_T04_10_1
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APLevel3.Qual
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APLevel3.Energy

/-!
# Part I, `PartI:T04/10/1`: `APLevel3Integrated` from its qualitative and energy leaves

Source of record: `the November 2 reference manuscript`, lines 285-288.

Statement: `apLevel3Integrated : APLevel3Integrated`, composed from `apLevel3Integrated_of`,
`APLevel3Qual` and `APLevel3Energy` (`Sub/PartI_T04_10_1.lean`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartI

/-- `APLevel3Integrated` (lines 285-288): the integrated second-jet energy inequality. -/
theorem apLevel3Integrated : APLevel3Integrated :=
  apLevel3Integrated_of apLevel3Qual apLevel3Energy

end UnforcedLeray.Short.PartI

end
