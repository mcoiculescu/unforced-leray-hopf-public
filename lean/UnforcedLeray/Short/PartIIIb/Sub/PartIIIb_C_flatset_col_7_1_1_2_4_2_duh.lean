import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_1_L1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_1_L2

/-!
# `sfcDuhamel`: `SFCDuhamel` from the lift and the Duhamel identity for a lift
(decomposition of `PartIII-b:C/flatset/col/7/1/1/2/4/2/1`)

Source `the November 2 reference manuscript` 1650-1656.
Immediate from `sfcDuhamel_of` (`sfcLiftEx` supplies the lift, `sfcDuhamelLift` the Duhamel identity).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem sfcDuhamel : SFCDuhamel :=
  sfcDuhamel_of sfcLiftEx sfcDuhamelLift

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
