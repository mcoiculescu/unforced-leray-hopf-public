import UnforcedLeray.Short.PartIIa.Sub.PartIIa_F09_3_1_1
import UnforcedLeray.Short.PartIIa.Tasks.F03aWindowEquation.RepLocInt
import UnforcedLeray.Short.PartIIa.Tasks.F09Adjoint.GraphBound.Window.Equation.AdjLocalIdentityOfPhaseOp
import UnforcedLeray.Short.PartIIa.Tasks.F09Adjoint.GraphBound.Window.Equation.AdjWindowChartU
import UnforcedLeray.Short.PartIIa.Tasks.F09Adjoint.GraphBound.Window.Equation.AdjWindowChartF
import UnforcedLeray.Short.PartIIa.Tasks.F09Adjoint.GraphBound.Window.Equation.AdjWindowTestIdentity

/-!
# Part II-a, task `PartII-a:F09/3/1/1`: the transformed adjoint equation

Assembly of the four leaves (`adjLocalIdentityOfPhaseOp`, `adjWindowChartU`, `adjWindowChartF`,
`adjWindowTestIdentity`) and `repLocInt` into `adjointWindowEquation_of`
(`Sub/PartII-a_F09_3_1_1.lean`). Source lines 1426-1442 of
`the November 2 reference manuscript`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIa

/-- **`PartII-a:F09/3/1/1`**: the transformed adjoint equation. -/
theorem adjointWindowEquation : AdjointWindowEquation :=
  adjointWindowEquation_of repLocInt adjLocalIdentityOfPhaseOp adjWindowChartU adjWindowChartF
    adjWindowTestIdentity

end UnforcedLeray.Short.PartIIa
