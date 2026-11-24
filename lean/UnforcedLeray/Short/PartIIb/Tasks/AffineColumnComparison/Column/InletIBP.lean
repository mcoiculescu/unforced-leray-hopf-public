import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_3_1
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.InletGood
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.RawGood
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.AbsPhaseIBP

/-!
# Part II-b, task `PartII-b:G4/3/1` (`InletIBP`)

Source of record: `the November 2 reference manuscript`, lines 2347-2348, 2370-2374,
2042-2046, 1206-1216, 1292.  The statement follows from the three leaves `inletGoodAll`
(`PartII-b:G4/3/1/1`), `rawGoodAll` (`PartII-b:G4/3/1/2`) and `absPhaseIBP` (`PartII-b:G4/3/1/3`)
via the decomposition `inletIBP_of` in `Sub/PartII-b_G4_3_1.lean`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

theorem inletIBP : UnforcedLeray.Short.IIb.InletIBP :=
  inletIBP_of inletGoodAll rawGoodAll absPhaseIBP

end UnforcedLeray.Short.IIb
