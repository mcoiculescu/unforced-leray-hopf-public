import UnforcedLeray.Short.PartIIa.Sub.N02_3_8
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.ZeroMode.Cutoff
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.ZeroMode.PrimSmooth
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.ZeroMode.PrimComm
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.ZeroMode.WindowBound
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.ZeroMode.GradCutError.GCEMinkowski
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.ZeroMode.StreamCutError.SCEPointwise
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.ZeroMode.StreamCutError.SCEIntegrable
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.ZeroMode.StreamCutError.SCEWin0
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.ZeroMode.StreamCutError.SCEWin1
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.ZeroMode.StreamCutError.SCEMom

/-!


Source of record: `the November 2 reference manuscript`, lines 1728-1735.
Composes the sibling Props proofs (`zeroCutoff`, `zeroPrimSmooth`, `zeroPrimComm`,
`zeroWindowBound`, `gCEMinkowski`) and the five StreamCutError lemma proofs
(`sCEPointwise`, `sCEIntegrable`, `sCEWin0`, `sCEWin1`, `sCEMom`) into `zeroStreamCutError_of`
(`Sub/N02_3_8.lean`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIa

theorem zeroStreamCutError : UnforcedLeray.Short.PartIIa.ZeroStreamCutError :=
  zeroStreamCutError_of zeroCutoff zeroPrimSmooth zeroPrimComm
    sCEPointwise sCEIntegrable gCEMinkowski zeroWindowBound
    sCEWin0 sCEWin1 sCEMom

end UnforcedLeray.Short.PartIIa
