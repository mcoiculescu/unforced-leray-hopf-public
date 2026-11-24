import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_4
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_4_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_4_2

/-!
# `SFCDuhamelGrad` (drafting task `PartIII-b:C/flatset/col/7/1/1/2/4/2/4`, theorem `sfcDuhamelGrad`)

Source `the November 2 reference manuscript` 1650-1656, 1684-1689, 3426-3430.

Composition: `sfcDuhamelGrad_of` applied to `sfcDuhamelEverywhere` (task `/4/1`) and
`sfcCausalHeatDiff` (task `/4/2`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem sfcDuhamelGrad : SFCDuhamelGrad :=
  sfcDuhamelGrad_of sfcDuhamelEverywhere sfcCausalHeatDiff

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
