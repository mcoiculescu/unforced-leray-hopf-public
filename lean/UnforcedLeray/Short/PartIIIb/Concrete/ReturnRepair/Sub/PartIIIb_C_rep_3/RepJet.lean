import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_3_3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_3_3.ChartTransfer
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_3_3.HessMerid
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_3_3.MeridEq

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **`RepJet` along the concrete sequence** (source 5212-5223, 5259-5268). -/
theorem repJet (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp)
    (hPG : D.PhaseGradient) : RepJet D :=
  repJet_of_pow4 repJetChartTransfer sepWXHessMeridPointwise_pow4 sepJetMeridEq D hst hPG

end UnforcedLeray.Short.PartIIIb.Concrete

end
