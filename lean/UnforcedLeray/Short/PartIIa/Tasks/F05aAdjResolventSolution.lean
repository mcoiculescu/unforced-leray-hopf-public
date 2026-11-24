import UnforcedLeray.Short.PartIIa.Sub.F05_1
import UnforcedLeray.Short.PartIIa.Tasks.F05aAdjResolventSolution.ParamIntegralSmooth
import UnforcedLeray.Short.PartIIa.Tasks.F05aAdjResolventSolution.OpsUnderIntegral
import UnforcedLeray.Short.PartIIa.Tasks.F05aAdjResolventSolution.TIntegralDecay
import UnforcedLeray.Short.PartIIa.Tasks.F05aAdjResolventSolution.AdjIntegrandRegular
import UnforcedLeray.Short.PartIIa.Tasks.F05aAdjResolventSolution.AdjIntegrandDeriv
import UnforcedLeray.Short.PartIIa.Tasks.F05aAdjResolventSolution.AdjIntegrandLimits
import UnforcedLeray.Short.PartIIa.Tasks.F05aAdjResolventSolution.AdjIntegrandDecay

/-!
# Part II-a, task `PartII-a:F05/1`: the adjoint resolvent of a phase test

Target: `AdjResolventSolution` (defined in `Short/PartII-a/Sub/F05.lean`, source lines 1403-1413).
The proof is the application of the conditional theorem `adjResolventSolution_of`
(`Sub/F05_1.lean`) to the seven proved step Props of the sibling task modules
`Tasks/F05aAdjResolventSolution/*.lean`.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartIIa

/-- Task `PartII-a:F05/1`: the adjoint resolvent of a phase test exists with the stated
smoothness, periodicity, equation and decay. Assembled from the seven step proofs. -/
theorem adjResolventSolution : AdjResolventSolution :=
  adjResolventSolution_of paramIntegralSmooth_proof opsUnderIntegral_proof tIntegralDecay_proof
    adjIntegrandRegular_proof adjIntegrandDeriv_proof adjIntegrandLimits_proof
    adjIntegrandDecay_proof

end UnforcedLeray.Short.PartIIa
