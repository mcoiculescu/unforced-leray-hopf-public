import UnforcedLeray.Short.PartIIb.Sub.G4_2_3_4
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.FrozenStream.Periodize.PerHarmonicCut.HcDerivDecay
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.FrozenStream.Periodize.PerHarmonicCut.PerSmoothSum
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.FrozenStream.Periodize.PerHarmonicCut.PerHarmonicFar

/-!
# Part II-b, item `PartII-b:G4/2/3/4` (`PerHarmonicCut`): assembly

Source of record: `the November 2 reference manuscript`, lines 2349-2358.

Applies `perHarmonicCut_of` to the three leaves `hcDerivDecay`, `perSmoothSum`
and `perHarmonicFar`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

theorem perHarmonicCut : UnforcedLeray.Short.IIb.PerHarmonicCut :=
  perHarmonicCut_of UnforcedLeray.Short.IIb.hcDerivDecay
    perSmoothSum
    UnforcedLeray.Short.IIb.perHarmonicFar

end UnforcedLeray.Short.IIb

end
