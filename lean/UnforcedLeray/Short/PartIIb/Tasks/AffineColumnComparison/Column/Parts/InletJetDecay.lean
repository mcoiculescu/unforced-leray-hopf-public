import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_3_7_4
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletProfileJets.CutStreamJets
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletProfileJets.SmoothVanish
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_3_7_4.RingStreamJetsDecay
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_3_7_4.CutStreamSVanish

/-!
# Part II-b, task `PartII-b:G4/3/7/4` (`InletJetDecay`), assembly

`inletJetDecay_of` applied to the four inputs `cutStreamJets`, `inletProfileSmoothVanish`,
`ringStreamJetsDecay` and `cutStreamSVanish`.
Source of record: `the November 2 reference manuscript`, lines 2347-2369.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

theorem inletJetDecay : UnforcedLeray.Short.IIb.InletJetDecay :=
  inletJetDecay_of cutStreamJets ringStreamJetsDecay inletProfileSmoothVanish cutStreamSVanish

end UnforcedLeray.Short.IIb
