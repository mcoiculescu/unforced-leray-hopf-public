import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1_org2_bound
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1_org2_bound.Sup
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1_org2_bound.Fderiv

/-!
# `duhamelSliceBound`: the slice bound of the Duhamel integral

Source `the November 2 reference manuscript` 1650-1656, 1684-1689.
The sup bound `duhamelSupBound` and the `x`-derivative bound `duhamelFderivBound` give the
slice bound through `duhamelSliceBound_of`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem duhamelSliceBound : DuhamelSliceBound :=
  duhamelSliceBound_of duhamelSupBound duhamelFderivBound

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
