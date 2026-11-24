import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N04_3_3_2
import UnforcedLeray.Short.PartIIa.Tasks.N04SmoothAdjoint.AdjointResidual.RepsVecAdjointOfWeakEq.MeridTestDense.OuterCore
import UnforcedLeray.Short.PartIIa.Tasks.N04SmoothAdjoint.AdjointResidual.RepsVecAdjointOfWeakEq.MeridTestDense.MeridProj

/-!
# `MeridCoreResolventDense` (task `PartII-a:N04/3/3/2`): assembly

Source of record: `the November 2 reference manuscript`,
lines 1456–1480 and 1838–1845, 3340–3363.
Assembles `meridCoreResolventDense` from `meridCoreResolventDense_of`,
`outerPhaseTestCoreDense`, and `meridProjOfPhaseTest`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIa

theorem meridCoreResolventDense : MeridCoreResolventDense :=
  meridCoreResolventDense_of outerPhaseTestCoreDense meridProjOfPhaseTest

end UnforcedLeray.Short.PartIIa
