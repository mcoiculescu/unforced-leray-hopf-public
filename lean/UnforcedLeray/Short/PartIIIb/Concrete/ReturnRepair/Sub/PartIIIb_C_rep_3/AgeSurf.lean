import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_3_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_3_1.JetSup
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_3_1.OutPrimSup
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_3_1.Decomp

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **`RepAgeSurf` along the concrete sequence** (source 5203-5210, 5236-5244). -/
theorem repAgeSurf (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) :
    RepAgeSurf D :=
  repAgeSurf_of sepJetPointwiseSup outPrimPointwiseSup sepWXWYPointwiseDecomp D hst

end UnforcedLeray.Short.PartIIIb.Concrete

end
