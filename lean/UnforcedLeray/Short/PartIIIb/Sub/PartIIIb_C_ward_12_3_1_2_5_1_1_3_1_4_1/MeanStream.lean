import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_1_4_1_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_1_4_1_2.A
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_1_4_1_2.B
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_1_4_1_2.C
import UnforcedLeray.Short.PartI.Tasks.TrainHeatFixed.TrainJetsBoundedFixed

/-!
# `PartIII-b:C/ward/12/3/1/2/5/1/1/3/1/4/1/2`: `meanStreamJetPoly`

Source `the November 2 reference manuscript` 397-404 and 427-446.
Assembles `MeanStreamJetPoly` from `meanStreamJetPoly_of` with
`hA := velJointJetsFixed3_of PartI.trainJetsBoundedFixed` (task /1, needs the pending PartI theorem
`trainJetsBoundedFixed`), `hB := meanStreamGradJets` (task /2), `hC := zeroFromGrad` (task /3).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem meanStreamJetPoly : MeanStreamJetPoly :=
  meanStreamJetPoly_of
    (velJointJetsFixed3_of UnforcedLeray.Short.PartI.trainJetsBoundedFixed)
    meanStreamGradJets
    zeroFromGrad

end UnforcedLeray.Short.PartIIIb.Concrete
