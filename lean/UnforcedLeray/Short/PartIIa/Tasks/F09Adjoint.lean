import UnforcedLeray.Short.PartIIa.Sub.PartIIa_F09
import UnforcedLeray.Short.PartIIa.Tasks.F09Adjoint.Existence
import UnforcedLeray.Short.PartIIa.Tasks.F09Adjoint.MaximalDomain
import UnforcedLeray.Short.PartIIa.Tasks.F09Adjoint.GraphBound

/-!
# Part II-a, task `PartII-a:F09`: decomposition of the adjoint at `r = 2`

Source `the November 2 reference manuscript` lines 1359-1361 and 1426-1442.
`commonBodyAdjoint` is `commonBodyAdjoint_of` (Sub `PartII-a_F09`) applied to the three leaves:
`adjointExistence` (task `PartII-a:F09/1`, Tasks/F09Adjoint/Existence.lean),
`adjointMaximalDomain` (task `PartII-a:F09/2`, Tasks/F09Adjoint/MaximalDomain.lean) and
`adjointGraphBound` (task `PartII-a:F09/3`, Tasks/F09Adjoint/GraphBound.lean).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIa

/-- **Task `PartII-a:F09`**: the adjoint at `r = 2`, `CommonBodyAdjoint`. -/
theorem commonBodyAdjoint : CommonBodyAdjoint :=
  commonBodyAdjoint_of adjointExistence adjointMaximalDomain adjointGraphBound

end UnforcedLeray.Short.PartIIa
