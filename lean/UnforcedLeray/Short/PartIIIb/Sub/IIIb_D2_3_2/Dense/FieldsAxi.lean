import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Sub.IIIb_D2_3_2_11_4
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Sub.IIIb_D2_3_2_11_4.Fderiv
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Sub.IIIb_D2_3_2_11_4.Lap
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Sub.IIIb_D2_3_2_11_4.Contractions
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Sub.IIIb_D2_3_2_11_4.DXp

/-!
# Axisymmetric no-swirl property of the Ward fields (`PartIII-b:IIIb-D2/3/2/11/4`, source 121-124, 6314-6316)

`wardFieldsAxi_proved : WardFieldsAxi`, assembled from the four equivariance facts
`fderivEqv_proved`, `lapEqv_proved`, `cdiffUUD2Eqv_proved`, `dxpEqv_proved` via `wardFieldsAxi_of`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem wardFieldsAxi_proved : WardFieldsAxi :=
  wardFieldsAxi_of fderivEqv_proved lapEqv_proved cdiffUUD2Eqv_proved dxpEqv_proved

end UnforcedLeray.Short.PartIIIb.Concrete
