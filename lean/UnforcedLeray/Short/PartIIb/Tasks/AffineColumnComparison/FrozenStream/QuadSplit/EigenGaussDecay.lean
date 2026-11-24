import UnforcedLeray.Short.PartIIb.Sub.G4_2_2_1
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.FrozenStream.QuadSplit.EigenRep
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.FrozenStream.QuadSplit.ACoefGauss
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.FrozenStream.QuadSplit.RqPolyAt
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.FrozenStream.QuadSplit.GaussMulPoly
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.FrozenStream.QuadSplit.GreenRemSmooth
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.FrozenStream.QuadSplit.PolyZpow

/-!
# Part II-b, task `PartII-b:G4/2/2/1`: `eigenGaussDecay`

Source of record: `the November 2 reference manuscript`, lines 2349-2352.

Proof: the reduction `eigenGaussDecay_of` applied to the six dependency leaves
(`eigenRep`, `aCoefGauss`, `rqPolyAt`, `gaussMulPoly`, `greenRemSmooth`, `polyZpow`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

theorem eigenGaussDecay : UnforcedLeray.Short.IIb.EigenGaussDecay :=
  eigenGaussDecay_of eigenRep aCoefGauss rqPolyAt gaussMulPoly greenRemSmooth polyZpow

end UnforcedLeray.Short.IIb
