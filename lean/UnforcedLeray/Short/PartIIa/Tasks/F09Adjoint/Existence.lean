import UnforcedLeray.Short.PartIIa.Sub.PartIIa_F09_1
import UnforcedLeray.Short.PartIIa.Tasks.F09Adjoint.Existence.Semigroup
import UnforcedLeray.Short.PartIIa.Tasks.F09Adjoint.Existence.Resolvent
import UnforcedLeray.Short.PartIIa.Tasks.F09Adjoint.Existence.Equation

/-!
# Part II-a, task `PartII-a:F09/1`: existence of the adjoint resolvent at `r = 2`

Source `the November 2 reference manuscript`, lines 1359-1361, 1403-1413,
1426-1440. The three sub-tasks `PartII-a:F09/1/1` (`Existence/Semigroup.lean`, `adjSemigroupBound`),
`PartII-a:F09/1/2` (`Existence/Resolvent.lean`, `adjResolventExists`) and `PartII-a:F09/1/3`
(`Existence/Equation.lean`, `adjResolventEquation`) are combined by `adjointExistence_of`
(Sub `PartII-a_F09_1`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIa

/-- **Task `PartII-a:F09/1`**: existence of the adjoint resolvent at `r = 2`. -/
theorem adjointExistence : AdjointExistence :=
  adjointExistence_of adjSemigroupBound adjResolventExists adjResolventEquation

end UnforcedLeray.Short.PartIIa
