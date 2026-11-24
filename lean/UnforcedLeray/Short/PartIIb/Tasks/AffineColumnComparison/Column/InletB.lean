import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_3_4
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.InletB.ChartAdv
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.InletB.RawDiff
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.InletB.InletDiff

/-!
# Part II-b, task `PartII-b:G4/3/4` (`inletBPtw`)

Source of record: `the November 2 reference manuscript`, SP 1919-1921, 2007-2012,
2370-2374, 2419. Assembly of the three leaves `PartII-b:G4/3/4/1` (`chartAdvPtw`),
`PartII-b:G4/3/4/2` (`rawProfDiffAt`), `PartII-b:G4/3/4/3` (`inletProfileDiffAt`) through
`inletBPtw_of` (Sub/PartII-b_G4_3_4.lean).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- **Pointwise inlet chart identity** (`InletBPtw`, SP 2370-2374, 2419): the composition of the
polarized advection identity, the raw-profile differentiability and the inlet-profile
differentiability. -/
theorem inletBPtw : UnforcedLeray.Short.IIb.InletBPtw :=
  inletBPtw_of chartAdvPtw rawProfDiffAt inletProfileDiffAt

end UnforcedLeray.Short.IIb
