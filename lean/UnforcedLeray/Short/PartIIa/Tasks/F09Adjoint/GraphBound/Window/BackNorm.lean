import UnforcedLeray.Short.PartIIa.Sub.PartIIa_F09_3_1_4
import UnforcedLeray.Short.PartIIa.Tasks.F09Adjoint.GraphBound.Window.BackNormMeas
import UnforcedLeray.Short.PartIIa.Tasks.F09Adjoint.GraphBound.Window.BackNormBound

/-!
# Part II-a, task `PartII-a:F09/3/1/4`: `AdjointWindowBackNorm` from the scalar chart bound

Assembles `AdjointWindowBackNorm` from the two scalar leaves `adjCompAEMeas`
(`PartII-a:F09/3/1/4/1`, `BackNormMeas.lean`) and `adjCompBound`
(`PartII-a:F09/3/1/4/2`, `BackNormBound.lean`) via `adjointWindowBackNorm_of`.
Source of record: `the November 2 reference manuscript`,
lines 1426-1442.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace UnforcedLeray.Short.PartIIa

/-- **`PartII-a:F09/3/1/4`: the norm of the transported adjoint Laplacian.** -/
theorem adjointWindowBackNorm : AdjointWindowBackNorm :=
  adjointWindowBackNorm_of adjCompAEMeas adjCompBound

end UnforcedLeray.Short.PartIIa
