import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_6_1_1_3_of
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_6_1_1_3_leaf1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_6_1_1_3_leaf2

/-!
# `FlatSolPair` (decomposition of `PartIII-b:C/flatset/col/7/1/1/2/6/1/1/3`)

Source `the November 2 reference manuscript`
1650-1656.  `FlatSolPair` follows from the two chart facts `FlatProductTest` (leaf1,
`flatProductTest`) and `FlatSlicePairing` (leaf2, `flatSlicePairing`) by `flatSolPair_of`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem flatSolPair : FlatSolPair :=
  flatSolPair_of flatProductTest flatSlicePairing

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
