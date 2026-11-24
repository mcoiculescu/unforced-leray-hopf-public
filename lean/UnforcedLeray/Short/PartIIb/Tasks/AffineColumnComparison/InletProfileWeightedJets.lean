import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_5_2_2_w
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletProfileJets.CutStreamJets
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletProfileJets.SmoothVanish
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_3_7_4.RingStreamJetsDecay
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_3_7_4.CutStreamSVanish

/-!
# Part II-b, task `PartII-b:G4/5/2/3` (`InletProfileWeightedJets`)

Source of record: `the November 2 reference manuscript`, lines 2356-2366, 2386-2387.
One-line assembly via `inletProfileWeightedJets_of`, using the accepted leaves `cutStreamJets`,
`ringStreamJetsDecay`, `inletProfileSmoothVanish` and `cutStreamSVanish`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

theorem inletProfileWeightedJets : UnforcedLeray.Short.IIb.InletProfileWeightedJets :=
  inletProfileWeightedJets_of cutStreamJets ringStreamJetsDecay inletProfileSmoothVanish
    cutStreamSVanish

end UnforcedLeray.Short.IIb
