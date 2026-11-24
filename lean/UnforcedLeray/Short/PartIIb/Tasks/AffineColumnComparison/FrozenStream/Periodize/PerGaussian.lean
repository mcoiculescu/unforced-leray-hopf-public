import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_2_3_3
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.FrozenStream.Periodize.PerGaussian.LatticeGauss
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.FrozenStream.Periodize.PerGaussian.GaussStrip
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.FrozenStream.Periodize.PerGaussian.PerDerivTsum

/-!
# Part II-b, task `PartII-b:G4/2/3/3` (`PerGaussian`): assembly

Source of record: `the November 2 reference manuscript`, lines 2349-2358.
Assembles the three leaves `G4/2/3/3/1` (`latticeGaussSum`), `G4/2/3/3/2` (`gaussStripLe`)
and `G4/2/3/3/3` (`perDerivTsum`) through `perGaussian_of`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

theorem perGaussian : UnforcedLeray.Short.IIb.PerGaussian :=
  perGaussian_of latticeGaussSum gaussStripLe perDerivTsum

end UnforcedLeray.Short.IIb
