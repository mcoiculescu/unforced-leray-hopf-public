import UnforcedLeray.Short.PartI.Sub.PartI_T04_10_1_2
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APLevel3.Energy.CutoffIneq
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APLevel3.Energy.Limit

/-!
# Part I, `PartI:T04/10/1/2`: the energy leaf `APLevel3Energy`

Source of record: `the November 2 reference manuscript`, lines 285-288
("Approximation and transverse cutoffs then give the velocity and vorticity energy identities").

Assembly only: `apLevel3Energy_of` (Sub/PartI_T04_10_1_2.lean) applied to the proved leaves
`apCutoffIneq_proof` (Energy/CutoffIneq.lean) and `apCutoffLimit_proof` (Energy/Limit.lean).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartI

/-- **`APLevel3Energy`** (lines 285-288): the energy leaf, assembled from the cutoff inequality
and the cutoff limit. -/
theorem apLevel3Energy : APLevel3Energy :=
  apLevel3Energy_of apCutoffIneq_proof apCutoffLimit_proof

end UnforcedLeray.Short.PartI

end
