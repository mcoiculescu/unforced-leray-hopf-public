import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.Glue
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.Window
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.PointDom
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.MajBin
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.StreamMajBin

/-!
# `PartIII-b:C/rep/5/1/2/4/1`: `WardYBinMassSeq`

Source `the November 2 reference manuscript` lines 5585-5593.
One-line application of `wardYBinMass_of` (`Glue.lean`) to `muWin_gt_quarter` (Window),
`wardYPointDomSeq` (PointDom), `wardYMajBinSeq` (MajBin), and `wardYStreamMajBinSeq`
(StreamMajBin).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem wardYBinMass (D : SeqData) {dm dp : ℝ} : D.WardYBinMassSeq dm dp :=
  wardYBinMass_of D (fun hst => muWin_gt_quarter D hst) (wardYPointDomSeq D) (wardYMajBinSeq D)
    (wardYStreamMajBinSeq D)

end UnforcedLeray.Short.PartIIIb.Concrete
