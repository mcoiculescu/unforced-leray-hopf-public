import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_1_1_org.Leaf5Proof

set_option autoImplicit false
noncomputable section
namespace UnforcedLeray.Short.IIIa

theorem freeFlowAvailExists (ν m : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t₁ t₂ b : ℝ) : UnforcedLeray.Short.IIIa.ComplFreeRateSub.FreeFlowAvailExists ν m tr t₁ t₂ b :=
  ComplFreeRateSub.freeFlowAvailExists_proof ν m tr t₁ t₂ b

end UnforcedLeray.Short.IIIa
