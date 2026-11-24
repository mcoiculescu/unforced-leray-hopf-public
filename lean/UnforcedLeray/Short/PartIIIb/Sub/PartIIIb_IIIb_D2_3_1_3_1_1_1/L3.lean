import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_3_1_3_1_1_1_3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_3_1_3_1_1_1_3.L1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_3_1_3_1_1_1_3.L2

/-!
# `farMajorantBound` (`PartIII-b:IIIb-D2/3/1/3/1/1/1/3`, assembled)

The two leaves `farMeas` (L1, measurability) and `farKernelL2` (L2, cylinder kernel bound)
feed `farMajorantBound_of` (Sub/PartIII-b_IIIb-D2_3_1_3_1_1_1_3.lean, Cauchy-Schwarz in `z`,
then the periodic block sum). Source 4155-4186, 3631-3646.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem farMajorantBound : FarMajorantBound :=
  farMajorantBound_of farMeas farKernelL2

end UnforcedLeray.Short.PartIIIb.Concrete
