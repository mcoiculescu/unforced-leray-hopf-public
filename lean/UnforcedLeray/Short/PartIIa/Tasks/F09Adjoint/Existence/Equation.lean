import UnforcedLeray.Short.PartIIa.Tasks.F09Adjoint.Existence.Equation.AdjPhaseTaylor
import UnforcedLeray.Short.PartIIa.Tasks.F09Adjoint.Existence.Equation.AdjTestGenOfTaylor

/-!
# Part II-a, task `PartII-a:F09/1/3`: the adjoint resolvent solves the adjoint equation

Source `the November 2 reference manuscript` lines 1359-1361, 1403-1413, 1426-1440.

The reduction `adjResolventEquation_of` (Sub `PartII-a_F09_1_3`) turns the Taylor expansion
`AdjPhaseTaylor` (task `PartII-a:F09/1/3/1`, file `Equation/AdjPhaseTaylor.lean`) and the passage
`AdjTestGenOfTaylor` (task `PartII-a:F09/1/3/2`, file `Equation/AdjTestGenOfTaylor.lean`) into
`AdjResolventEquation`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIa

/-- **Task `PartII-a:F09/1/3`**: the adjoint resolvent solves the adjoint equation. -/
theorem adjResolventEquation : AdjResolventEquation :=
  adjResolventEquation_of adjPhaseTaylor adjTestGenOfTaylor

end UnforcedLeray.Short.PartIIa
