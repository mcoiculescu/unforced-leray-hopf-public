import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_5
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletContDiff
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletJetBound

/-!
# Part II-b, task `PartII-b:G4/5` (`InletSupBound`): assembly

Source of record: `the November 2 reference manuscript` lines 2347-2369 and
2383-2385. One-line assembly `inletSupBound_of inletContDiff inletJetBound`, using the accepted
leaves `inletContDiff` (task `PartII-b:G4/5/1`) and `inletJetBound` (task `PartII-b:G4/5/2`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

theorem inletSupBound : UnforcedLeray.Short.IIb.InletSupBound :=
  inletSupBound_of inletContDiff inletJetBound

end UnforcedLeray.Short.IIb
