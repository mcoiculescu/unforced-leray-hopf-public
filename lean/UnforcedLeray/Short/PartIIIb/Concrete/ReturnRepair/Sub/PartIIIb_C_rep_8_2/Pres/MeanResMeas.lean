import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_6
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_6.AxisEv

/-!
# `PartIII-b:C/rep/8/2/pres/6`: assembly of `meanResMeas`

Source `the November 2 reference manuscript`
lines 1205-1225, 4139-4141, 4776-4791, 5272-5289.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem meanResMeas (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) : D.MeanResMeas :=
  meanResMeas_of_axis D hst (axisEv D hst)

end UnforcedLeray.Short.PartIIIb.Concrete
