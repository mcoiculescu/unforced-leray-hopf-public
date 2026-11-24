import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_2
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_2_5
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_2_5.L1
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_2_5.L3
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_2_5.L4
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_2_5.L5
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_2_5.L6

/-!
# `sepGapMajorantIntegrable` (`PartIII-b:IIIb-D2/3/1/1/2/5`), unconditional

Assembles the five proved hypotheses of `sepGapMajorantIntegrable_of`:
measurability (`l5Meas`), Cauchy-Schwarz in `z` (`l5Holder`), periodic block sum (`l5PerSum`),
change of variables `l = e^s` (`l5ChangeVar`) and the `L²_τL²_z` moment (`l5Moment`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem sepGapMajorantIntegrable : SepGapMajorantIntegrable :=
  sepGapMajorantIntegrable_of l5Meas l5Holder l5PerSum l5ChangeVar l5Moment

end UnforcedLeray.Short.PartIIIb.Concrete
