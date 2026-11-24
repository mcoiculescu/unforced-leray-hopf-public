import UnforcedLeray.Short.PartIIa.Sub.PartIIa_F09_3_1_3
import UnforcedLeray.Short.PartIIa.Tasks.F09Adjoint.GraphBound.Window.BackRealIdentity
import UnforcedLeray.Short.PartIIa.Tasks.F09Adjoint.GraphBound.Window.BackLambdaInt

/-!


Source `the November 2 reference manuscript`
lines 1426-1442 (the reversed window). Immediate assembly of the two chart leaves
`adjBackRealIdentity` (task 3/2) and `adjBackLambdaInt` (task 3/3) through the conditional
`adjointWindowBackEquation_of` of `Sub/PartII-a_F09_3_1_3.lean`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIa

theorem adjointWindowBackEquation : AdjointWindowBackEquation :=
  adjointWindowBackEquation_of adjBackRealIdentity adjBackLambdaInt

end UnforcedLeray.Short.PartIIa
