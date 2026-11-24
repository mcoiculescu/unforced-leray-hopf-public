import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_2
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.MeanSmooth
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.MeanXHess
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.MeanXTaylor
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.MeanYHess
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.MeanYTaylor

/-!
# `PartIII-b:C/rep/8/2/2/6`: the mean jet estimate `MeanJet`

Assembles the mean jet bound `D.MeanJet` from the five component estimates:
the smoothness `meanSmooth`, the transverse Hessian `meanXHess`, the Y Hessian `meanYHess`,
and the Taylor estimates `meanXTaylor`, `meanYTaylor`, via `meanJet_of`
(`Sub/PartIII-b_C_rep_8_2_2.lean`, source `the November 2 reference manuscript`
5438-5448).
-/

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem meanJet (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) : D.MeanJet :=
  meanJet_of D hst (meanXTaylor D (meanXHess D) (meanSmooth D))
    (meanYTaylor D (meanYHess D) (meanSmooth D)) (meanXHess D)

end UnforcedLeray.Short.PartIIIb.Concrete
