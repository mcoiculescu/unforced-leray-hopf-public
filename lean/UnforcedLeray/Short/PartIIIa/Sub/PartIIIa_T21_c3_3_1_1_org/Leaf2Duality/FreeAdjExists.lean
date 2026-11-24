import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_1_1_2_2_2_1
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_1_1_org.Leaf2Duality.FreeAdjExists.FreeSpSmoothRep
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_1_1_org.Leaf2Duality.FreeAdjExists.FreePointwisePde

theorem freeAdjExists (ν m : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t₁ t₂ : ℝ) :
    UnforcedLeray.Short.IIIa.ComplFreeRateSub.Leaf2DualityNeeded.FreeAdjExists ν m tr t₁ t₂ :=
  UnforcedLeray.Short.IIIa.ComplFreeRateSub.Leaf2DualityNeeded.freeAdjExists_of ν m tr t₁ t₂
    (fun s => UnforcedLeray.Short.IIIa.ComplFreeRateSub.Leaf2DualityNeeded.freeSpSmoothRep (ν ^ (-2 : ℝ)) m t₁ s)
    (fun s => UnforcedLeray.Short.IIIa.ComplFreeRateSub.Leaf2DualityNeeded.freePointwisePde ν m tr t₁ s)
