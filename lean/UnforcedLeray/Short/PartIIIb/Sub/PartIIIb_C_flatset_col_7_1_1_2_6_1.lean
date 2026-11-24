import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_6_1_of
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_6_1_1

/-!
# `SFCDivAE` (decomposition of `PartIII-b:C/flatset/col/7/1/1/2/6/1`)

Source `the November 2 reference manuscript`
1650-1656. The weak identity `sfcDivWeak` (in `_1_1`) is upgraded to the a.e. identity `SFCDivAE`
by `sfcDivAE_of` (in `_1_of`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem sfcDivAE : SFCDivAE :=
  sfcDivAE_of sfcDivWeak

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
