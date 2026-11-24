import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_2_L1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_2_L2

/-!
# `SFCHeatGrad` (source 3426-3430): assembly of gradient commutation and Gaussian Jensen

Task `PartIII-b:C/flatset/col/7/1/1/2/4/2/2`, the immediate assembly
`sfcHeatGrad_of sfcHeatCommute sfcHeatJensen` (`sfcHeatCommute` from `_L1.lean`,
`sfcHeatJensen` from `_L2.lean`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem sfcHeatGrad : SFCHeatGrad :=
  sfcHeatGrad_of sfcHeatCommute sfcHeatJensen

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
