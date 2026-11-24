import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N04_3_3_Org
import UnforcedLeray.Short.PartIIa.Tasks.N04SmoothAdjoint.AdjointResidual.RepsVecAdjointOfWeakEq.LeftOnCore
import UnforcedLeray.Short.PartIIa.Tasks.N04SmoothAdjoint.AdjointResidual.RepsVecAdjointOfWeakEq.CoreMemLp
import UnforcedLeray.Short.PartIIa.Tasks.N04SmoothAdjoint.AdjointResidual.RepsVecAdjointOfWeakEq.MeridTestDense

/-!
# `PartII-a:N04/3/3`: `RepsVecAdjointOfWeakEqCore`

Source: `the November 2 reference manuscript` lines 1842-1845.
Assembles `repsVecAdjointOfWeakEqCore` from `repsVecAdjointOfWeakEqCore_of`,
`repsVecLeftOnCore`, `meridCoreTestMemLp`, and `meridCoreResolventDense`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIa

theorem repsVecAdjointOfWeakEqCore : RepsVecAdjointOfWeakEqCore :=
  repsVecAdjointOfWeakEqCore_of repsVecLeftOnCore meridCoreTestMemLp meridCoreResolventDense

end UnforcedLeray.Short.PartIIa
