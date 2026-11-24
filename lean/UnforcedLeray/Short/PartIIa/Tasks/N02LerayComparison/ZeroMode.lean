import UnforcedLeray.Short.PartIIa.Sub.N02_3
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.ZeroMode.FlatSolenoid
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.ZeroMode.FlatGradient
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.ZeroMode.CutTest
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.ZeroMode.GradCutError
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.ZeroMode.StreamCutError

/-!
# Part II-a, task `PartII-a:N02/3`: assembly of `NearLerayZeroMode`

Source of record: `the November 2 reference manuscript`, lines 1728-1737.
The target is closed by the conditional top-layer theorem `nearLerayZeroMode_of` (`Sub/N02_3.lean`)
applied to the compiled leaf theorems `zeroFlatSolenoid`, `zeroFlatGradient`, `zeroCutTest`,
`zeroGradCutError`, `zeroStreamCutError`.
-/

namespace UnforcedLeray.Short.PartIIa

theorem nearLerayZeroMode_proof : UnforcedLeray.Short.PartIIa.NearLerayZeroMode :=
  nearLerayZeroMode_of (zeroFlatProj_of zeroFlatSolenoid zeroFlatGradient)
    (zeroGradApprox_of zeroCutTest zeroGradCutError)
    (zeroStreamApprox_of zeroCutTest zeroStreamCutError)

end UnforcedLeray.Short.PartIIa
