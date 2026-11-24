import UnforcedLeray.Short.PartIIa.Sub.PartIIa_F09_3_1
import UnforcedLeray.Short.PartIIa.Tasks.F09Adjoint.GraphBound.Window.Equation
import UnforcedLeray.Short.PartIIa.Tasks.F09Adjoint.GraphBound.Window.Norms
import UnforcedLeray.Short.PartIIa.Tasks.F09Adjoint.GraphBound.Window.BackEquation
import UnforcedLeray.Short.PartIIa.Tasks.F09Adjoint.GraphBound.Window.BackNorm

/-!
# Part II-a, task `PartII-a:F09/3/1`: the time-reversed diffusion bound (unconditional)

Source of record `the November 2 reference manuscript`
lines 1426-1442 and 1431-1480. Assembles the four leaves
`adjointWindowEquation` (F09/3/1/1), `adjointWindowNorms` (F09/3/1/2),
`adjointWindowBackEquation` (F09/3/1/3), `adjointWindowBackNorm` (F09/3/1/4)
through `adjointLocalWindowEstimate_of` and `adjointLaplacianBound_of`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIa

/-- **`PartII-a:F09/3/1`: the time-reversed diffusion bound.** -/
theorem adjointLaplacianBound : AdjointLaplacianBound :=
  adjointLaplacianBound_of
    (adjointLocalWindowEstimate_of adjointWindowEquation adjointWindowNorms
      adjointWindowBackEquation adjointWindowBackNorm)

end UnforcedLeray.Short.PartIIa
