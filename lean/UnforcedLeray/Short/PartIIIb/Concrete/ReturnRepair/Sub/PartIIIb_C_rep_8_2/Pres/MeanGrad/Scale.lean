import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.Pres.MeanGrad.Sub.PartIIIb_C_rep_8_2_pres_5_3
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.Pres.MeanGrad.Sub.PartIIIb_C_rep_8_2_pres_5_3_1
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.Pres.MeanGrad.Sub.PartIIIb_C_rep_8_2_pres_5_3_2
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.Pres.MeanGrad.Sub.PartIIIb_C_rep_8_2_pres_5_3_3
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.Pres.MeanGrad.Sub.PartIIIb_C_rep_8_2_pres_5_3_4
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.Pres.MeanGrad.Sub.PartIIIb_C_rep_8_2_pres_5_3_5
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2.Pres.MeanGrad.Sub.PartIIIb_C_rep_8_2_pres_5_3_6

/-!
# `meanJetScaleBound` (`PartIII-b:C/rep/8/2/pres/5/3`, Scale)

Assembles the six calculus leaves `trFd trPd trPd2 scD1 scD2 scLap` into the
scaled jet bound `MeanJetScaleBound` through `meanJetScaleBound_of`.
Source of record: `shorter-proof-2026-11-02.tex` lines 4784, 5455, 5267-5268.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem meanJetScaleBound : MeanJetScaleBound :=
  meanJetScaleBound_of trFd trPd trPd2 scD1 scD2 scLap

end UnforcedLeray.Short.PartIIIb.Concrete
