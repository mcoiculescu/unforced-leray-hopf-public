import UnforcedLeray.Short.PartIIa.Sub.F14_1_org
import UnforcedLeray.Short.PartIIa.Tasks.F14SmoothStressMap.CoreDense.FwdRegular
import UnforcedLeray.Short.PartIIa.Tasks.F14SmoothStressMap.CoreDense.FwdDeriv
import UnforcedLeray.Short.PartIIa.Tasks.F14SmoothStressMap.CoreDense.FwdDecay
import UnforcedLeray.Short.PartIIa.Tasks.F14SmoothStressMap.CoreDense.Remainder

/-!
# Part II-a, `PartII-a:F14/1/1`: `D2CoreDense` from the four forward leaves

Source of record: `the November 2 reference manuscript`, lines 1456-1467.
`d2CoreDense_of_leaves` (Sub/F14_1_org.lean) reduces `D2CoreDense` to the four leaves
`FwdIntegrandRegular`, `FwdIntegrandDeriv`, `FwdIntegrandDecay` and `FwdRemainderBound`, each
proved in the `CoreDense/` folder.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace UnforcedLeray.Short.PartIIa

theorem d2CoreDense : D2CoreDense :=
  d2CoreDense_of_leaves fwdIntegrandRegular fwdIntegrandDeriv fwdIntegrandDecay fwdRemainderBound

end UnforcedLeray.Short.PartIIa
