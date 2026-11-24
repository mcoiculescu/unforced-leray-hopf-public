import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1.SmoothOf
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1.SmoothLeaf1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1.SmoothLeaf2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1.SmoothLeaf3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1.SmoothLeaf4
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1.SmoothLeaf5
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1.SmoothLeaf6

/-!
# `DuhamelSmooth` (task `PartIII-b:C/flatset/col/7/1/1/2/1/org2/smooth`)

Assembles the six leaves: `duhamelShift` (Leaf 1), `rhoCutSmooth` (Leaf 2), `heatSmooth`
(Leaf 3), `heatBound` (Leaf 4), `heatCont` (Leaf 5) and `paramIntegralSmooth` (Leaf 6)
into `duhamelSmooth_of` from `SmoothOf`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem duhamelSmooth : DuhamelSmooth :=
  duhamelSmooth_of duhamelShift rhoCutSmooth heatSmooth heatBound heatCont paramIntegralSmooth

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
