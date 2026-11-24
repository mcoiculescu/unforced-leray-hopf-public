import UnforcedLeray.Short.PartIIa.Sub.N02_4_5.Gen
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.ModeSolve.GreenKey1D
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.ModeSolve.GreenKey2D
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.ModeSolve.GenHyp
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.ModeSolve.ConvFderiv
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.ModeSolve.ConvIntegrable
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.ModeSolve.ConvDecay

/-!
# Part II-a, task `PartII-a:N02/4/5` (`NzModeSolve`): assembly of the target

Composes the six leaf theorems with the conditional reduction `nzModeSolve_of`
(`Sub/N02_4_5/Cond.lean`) and the smoothness reduction `nzConvSmooth_of`
(`Sub/N02_4_5/Gen.lean`). No hypotheses beyond the leaves.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartIIa

/-- **`NzModeSolve` (task `PartII-a:N02/4/5`).** -/
theorem nzModeSolve : UnforcedLeray.Short.PartIIa.NzModeSolve :=
  nzModeSolve_of (nzGreenKey2D_of nzGreenKey1D_proof) (nzConvSmooth_of nzConvGenHyp_proof)
    (nzConvFderiv_of nzConvGenHyp_proof) nzConvIntegrable_proof (nzConvDecay_of nzConvGenHyp_proof)

#print axioms nzModeSolve

end UnforcedLeray.Short.PartIIa
