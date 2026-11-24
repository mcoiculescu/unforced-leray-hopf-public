import UnforcedLeray.Short.PartIIa.Sub.PartIIa_F09_1_3_1
import UnforcedLeray.Short.PartIIa.Tasks.F09Adjoint.Existence.Equation.PhaseDuality
import UnforcedLeray.Short.PartIIa.Tasks.F09Adjoint.Existence.Equation.SliceFwdCombine

/-!
# Part II-a, task `PartII-a:F09/1/3/1`: `adjPhaseTaylor`

Source `the November 2 reference manuscript` lines 1403-1413, 1426-1428.
Immediate from `adjPhaseTaylor_of` (Taylor expansion of the adjoint phase semigroup from the
slicewise forward Taylor bound and Hilbert duality), applied to `sliceFwdTaylor_all`
(task 1/3/1/4) and `phaseDualityAdjT` (task 1/3/1/3).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIa

/-- **Task `PartII-a:F09/1/3/1`**: Taylor expansion of the adjoint phase semigroup on a phase test. -/
theorem adjPhaseTaylor : AdjPhaseTaylor :=
  adjPhaseTaylor_of sliceFwdTaylor_all phaseDualityAdjT

end UnforcedLeray.Short.PartIIa
