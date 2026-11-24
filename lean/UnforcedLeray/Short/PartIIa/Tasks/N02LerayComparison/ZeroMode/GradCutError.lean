import UnforcedLeray.Short.PartIIa.Sub.N02_3_7
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.ZeroMode.Cutoff
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.ZeroMode.PrimSmooth
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.ZeroMode.PrimComm
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.ZeroMode.WindowBound
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.ZeroMode.GradCutError.GCEPointwise
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.ZeroMode.GradCutError.GCEIntegrable
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.ZeroMode.GradCutError.GCEMinkowski
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.ZeroMode.GradCutError.GCEWin0
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.ZeroMode.GradCutError.GCEWin1
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.ZeroMode.GradCutError.GCEMom

/-!


Source of record: `the November 2 reference manuscript`, lines 1728-1735.
Composes the four sibling Props proofs (`zeroCutoff`, `zeroPrimSmooth`, `zeroPrimComm`,
`zeroWindowBound`) and the six GradCutError lemma proofs into `zeroGradCutError_of`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.Short.PartIIa.ZeroGradCutErrorAux

theorem zeroGradCutError : UnforcedLeray.Short.PartIIa.ZeroGradCutError :=
  zeroGradCutError_of zeroCutoff zeroPrimSmooth zeroPrimComm zeroWindowBound
    gCEPointwise GCEIntegrableAux.gCEIntegrable gCEMinkowski gCEWin0 gCEWin1 gCEMom

end UnforcedLeray.Short.PartIIa
