import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_6_1_1_of
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_6_1_1_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_6_1_1_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_6_1_1_3

/-!
# `SFCDivWeak` (decomposition of `PartIII-b:C/flatset/col/7/1/1/2/6/1/1`)

Source `the November 2 reference manuscript`
1650-1656. The three source facts `FlatLift`, `FlatResSol`, `FlatSolPair` (leaves `_1`, `_2`, `_3`)
feed the reduction `sfcDivWeak_of` (in `_of`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem sfcDivWeak : SFCDivWeak :=
  sfcDivWeak_of flatLift flatResSol flatSolPair

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
