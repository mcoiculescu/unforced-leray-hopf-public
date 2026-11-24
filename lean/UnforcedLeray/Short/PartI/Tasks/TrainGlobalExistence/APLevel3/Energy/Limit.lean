import UnforcedLeray.Short.PartI.Sub.PartI_T04_10_1_2_2
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APLevel3.Energy.Limit.CellIntegrable
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APLevel3.Energy.Limit.Measurable

/-!
# Part I, `PartI:T04/10/1/2/2`: `APCutoffLimit` from its three analytic leaves

Source of record: `the November 2 reference manuscript`, lines 285-288
(approximation and transverse cutoffs; `R → ∞` by dominated convergence).

Statement: `apCutoffLimit_proof : APCutoffLimit`, composed from `apCutoffLimit_of`,
`cellVortJetIntegrable_proof` and `cutoffVortJetMeasurable_proof`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartI

/-- `APCutoffLimit` (lines 285-288): the transverse cutoff energies converge as `R → ∞`. -/
theorem apCutoffLimit_proof : APCutoffLimit :=
  apCutoffLimit_of cellVortJetIntegrable_proof cutoffVortJetMeasurable_proof

end UnforcedLeray.Short.PartI

end
