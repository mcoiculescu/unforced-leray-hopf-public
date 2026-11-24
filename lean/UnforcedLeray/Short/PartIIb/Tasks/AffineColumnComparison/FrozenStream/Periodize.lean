import UnforcedLeray.Short.PartIIb.Sub.G4_2_3
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.FrozenStream.Periodize.CutExists
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.FrozenStream.Periodize.CoreGaussian
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.FrozenStream.Periodize.PerGaussian
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.FrozenStream.Periodize.PerHarmonicCut

/-!
# Part II-b, task `PartII-b:G4/2/3` (`PeriodizeCoreCut`): assembly

Source: `the November 2 reference manuscript`, lines 2349-2358.

Assembles `periodizeCoreCut` from the four leaf theorems `cutExists`, `coreGaussian`,
`perGaussian`, `perHarmonicCut` (leaves `PartII-b:G4/2/3/1` to `/4`) via the compiled
conditional theorem `periodizeCoreCut_of`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

theorem periodizeCoreCut : UnforcedLeray.Short.IIb.PeriodizeCoreCut :=
  periodizeCoreCut_of cutExists coreGaussian perGaussian perHarmonicCut

end UnforcedLeray.Short.IIb
