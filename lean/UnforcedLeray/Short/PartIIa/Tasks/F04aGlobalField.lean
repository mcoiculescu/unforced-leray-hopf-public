import UnforcedLeray.Short.PartIIa.Sub.PartIIa_F04_1
import UnforcedLeray.Short.PartIIa.Tasks.F04aGlobalField.WindowLapAEMeas
import UnforcedLeray.Short.PartIIa.Tasks.F04aGlobalField.WindowLapLocInt
import UnforcedLeray.Short.PartIIa.Tasks.F04aGlobalField.WindowRhsFinite
import UnforcedLeray.Short.PartIIa.Tasks.F04aGlobalField.WindowLapUnique
import UnforcedLeray.Short.PartIIa.Tasks.F04aGlobalField.WindowLapGlue
import UnforcedLeray.Short.PartIIa.Tasks.F04aGlobalField.WindowLapPoU
import UnforcedLeray.Short.PartIIa.Tasks.F04aGlobalField.WindowLapPeriodic

/-!
# Part II-a, task `PartII-a:F04/1`: the global window Laplacian field

Composition of the seven leaves of `Tasks/F04aGlobalField/` through
`globalLaplacianField_of` (`Sub/PartIIa_F04_1.lean`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIa

theorem globalLaplacianField : UnforcedLeray.Short.PartIIa.GlobalLaplacianField :=
  globalLaplacianField_of windowLapAEMeas windowLapLocInt windowRhsFinite windowLapUnique
    windowLapGlue windowLapPoU (windowLapPeriodic_of windowLapUnique)

end UnforcedLeray.Short.PartIIa

#print axioms UnforcedLeray.Short.PartIIa.globalLaplacianField
