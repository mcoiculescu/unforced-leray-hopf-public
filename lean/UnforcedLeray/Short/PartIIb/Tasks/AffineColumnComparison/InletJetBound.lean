import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_5_2
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.RingLiftJet
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletProfileWeightedJets

/-!
# Part II-b, task `PartII-b:G4/5/2` (`InletJetBound`): assembly

Source of record: `the November 2 reference manuscript` lines 2346-2366, 2386-2387.
One-line assembly `inletJetBound_of ringLiftJet inletProfileWeightedJets`, using the accepted
leaves `ringLiftJet` (task `PartII-b:G4/5/2/1`) and `inletProfileWeightedJets` (task
`PartII-b:G4/5/2/3`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

theorem inletJetBound : UnforcedLeray.Short.IIb.InletJetBound :=
  inletJetBound_of ringLiftJet inletProfileWeightedJets

end UnforcedLeray.Short.IIb
