import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_2_1_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_2_1_1.GaussInt
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_2_1_1.ShiftDeriv
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_2_1_1.GaussIBP

/-!
# `SFCHeatHasDerivDir` (source 3426-3430): assembly of the four lemmas

Source `the November 2 reference manuscript`
3426-3430. The four Gaussian lemmas are proved in the `_1_1` folder (`GaussInt`, `ShiftDeriv`,
`GaussIBP`, `GaussPeriodic`); `sfcHeatHasDerivDir_of` in the `_1_1` file combines them.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem sfcHeatHasDerivDir : SFCHeatHasDerivDir :=
  sfcHeatHasDerivDir_of sfcGaussWeightedInt sfcGaussShiftDeriv sfcGaussIBP

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
