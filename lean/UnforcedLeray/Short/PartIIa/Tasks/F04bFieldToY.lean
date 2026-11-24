import UnforcedLeray.Short.PartIIa.Sub.PartIIa_F04_2
import UnforcedLeray.Short.PartIIa.Tasks.F04bFieldToY.PeriodicFieldToYq
import UnforcedLeray.Short.PartIIa.Tasks.F04bFieldToY.PeriodPartition
import UnforcedLeray.Short.PartIIa.Tasks.F04bFieldToY.PeriodUnfold
import UnforcedLeray.Short.PartIIa.Tasks.F04bFieldToY.WindowTestIdentity
import UnforcedLeray.Short.PartIIa.Tasks.F04bFieldToY.PhasePairSliceIntegrable

/-!
# Part II-a, task `PartII-a:F04/2`: from a global window Laplacian to `HasPhaseOp (νΔ)`

Composition of the five leaves of `Tasks/F04bFieldToY/` through `laplacianFieldToY_of`
(`Sub/PartIIa_F04_2.lean`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIa

theorem laplacianFieldToY : UnforcedLeray.Short.PartIIa.LaplacianFieldToY :=
  laplacianFieldToY_of periodicFieldToYq_proof periodPartition_proof periodUnfold_proof
    windowTestIdentity_proof phasePairSliceIntegrable_proof

end UnforcedLeray.Short.PartIIa

#print axioms UnforcedLeray.Short.PartIIa.laplacianFieldToY
