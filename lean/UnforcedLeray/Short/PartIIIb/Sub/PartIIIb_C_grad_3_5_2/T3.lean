import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_5_2_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_5_2_2.ExpJets
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_5_2_2.AgeInv
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_5_2_2.AyJetBounds

/-!
# `PartIII-b:C/grad/3/5/2/2` task T3: `PsipALocUnif` from the jet inputs

Assembles `psipALocUnif_of` (aggregator `Sub/PartIII-b_C_grad_3_5_2_2.lean`) with the three
jet inputs: `psijExpJets` (`ExpJets.lean`), `ageInvJets` (`AgeInv.lean`) and `ayJets`
(`AyJetBounds.lean`).  Source 5063-5079, 4974-4980.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem psipALocUnif (as : ℝ) : PsipALocUnif as :=
  psipALocUnif_of as (psijJets_of psijExpJets ageInvJets) (ayJets as)

end UnforcedLeray.Short.PartIIIb.Concrete
