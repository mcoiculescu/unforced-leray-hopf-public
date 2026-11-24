import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_4_2_of
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_4_2_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_4_2_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_4_2_3

/-!
# `SFCCausalHeatDiff` (drafting task `PartIII-b:C/flatset/col/7/1/1/2/4/2/4/2`)

Source `the November 2 reference manuscript` 3426-3430, 1650-1656.

Composition: the regular datum `sfcDatumReg`, the heat bounds `sfcHeatBounds` and the
parametric measurability `sfcHeatParamMeas` feed the dominated-differentiation theorem
`sfcCausalHeatDiff_of`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem sfcCausalHeatDiff : SFCCausalHeatDiff :=
  sfcCausalHeatDiff_of sfcDatumReg sfcHeatBounds sfcHeatParamMeas

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
