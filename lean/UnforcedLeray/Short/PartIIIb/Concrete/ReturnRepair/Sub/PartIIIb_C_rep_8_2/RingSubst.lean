import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_6
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.RingSubst.Term1
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.RingSubst.Term2
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.RingSubst.Term3
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.RingSubst.Term4

/-!
# `PartIII-b:C/rep/8/2/6` (substitution): the ring substitution from the four Ward terms

Source `the November 2 reference manuscript` 5460-5477 (ring-chart rules and the
four-term substitution), 5438-5448 (mean jets), 5449-5453 (clock).

The four term estimates `ringTerm1_of`..`ringTerm4_of` (files `RingSubst/Term1..Term4`) are
combined by `SeqData.ringSubst_of_terms` (Sub/PartIII-b_C_rep_8_2_6.lean).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **Ring substitution along the sequence** (source 5460-5477): the four term estimates
combined by `SeqData.ringSubst_of_terms`. -/
theorem ringSubst_of (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) (h6 : D.ActualJet)
    (h7 : D.JetClock) (h1 : D.RingChartRules) (h2 : D.MeanJet) (h3 : D.TrainMoment) :
    D.RingSubst :=
  D.ringSubst_of_terms hst (ringTerm1_of D hst h6 h7 h1 h2 h3) (ringTerm2_of D hst h6 h7 h1 h2 h3)
    (ringTerm3_of D hst h6 h7 h1 h2 h3) (ringTerm4_of D hst h6 h7 h1 h2 h3)

end UnforcedLeray.Short.PartIIIb.Concrete
