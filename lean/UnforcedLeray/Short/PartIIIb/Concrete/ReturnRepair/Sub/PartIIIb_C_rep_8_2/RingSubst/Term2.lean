import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_6_2
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.RingSubst.Term2D1
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.RingSubst.Term2D2
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.RingSubst.Term2Symm

/-!
# `PartIII-b:C/rep/8/2/6/2`: Term 2 of the four-term substitution, from the three train facts

Source `the November 2 reference manuscript` lines 5470-5475.  The three
train-derivative facts (`TrainFlatD1Bound`, `TrainFlatD2Bound`, `TrainFlatD2Symm`) are proved in
`RingSubst.Term2D1`, `RingSubst.Term2D2` and `RingSubst.Term2Symm`; this file applies the
sequence-level composition `ringTerm2_of_of` to them.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **Term 2 along the sequence** (source 5470-5475): the composition of `ringTerm2_of_of` with the
three proved train-derivative facts. -/
theorem ringTerm2_of (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) (h6 : D.ActualJet)
    (h7 : D.JetClock) (h1 : D.RingChartRules) (h2 : D.MeanJet) (h3 : D.TrainMoment) :
    D.RingTerm2 :=
  ringTerm2_of_of D hst h6 h7 h1 h2 h3 trainFlatD1Bound trainFlatD2Bound trainFlatD2Symm

end UnforcedLeray.Short.PartIIIb.Concrete
