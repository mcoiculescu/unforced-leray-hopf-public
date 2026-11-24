import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_6_1.BjetYoung
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_6_1.Term1Pointwise

/-!
# `PartIII-b:C/rep/8/2/6/1`: term 1 of the ring substitution

Source `the November 2 reference manuscript` 5470-5472 (error of `2U·∇Y`),
5438-5448 (mean jets), 5449-5453 (clock), 5460-5465 (ring-chart rules).

Composes the two lemmas `bjetYoung_of` (from `ActualJet`, `JetClock`) and `term1Pointwise`
into `ringTerm1_of_lemmas` (Sub/PartIII-b_C_rep_8_2_6_1.lean).
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Term 1 of the ring substitution along the sequence (source 5470-5472). -/
theorem ringTerm1_of (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) (h6 : D.ActualJet)
    (h7 : D.JetClock) (h1 : D.RingChartRules) (h2 : D.MeanJet) (h3 : D.TrainMoment) :
    D.RingTerm1 :=
  ringTerm1_of_lemmas D hst (bjetYoung_of D hst h6 h7) term1Pointwise h1 h2 h3

end UnforcedLeray.Short.PartIIIb.Concrete
