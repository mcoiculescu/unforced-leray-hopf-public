import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_4_1_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_4_1_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_4_1_3

/-!
# `SFCDuhamelEverywhere`: assembly of the three regularity lemmas
(drafting task `PartIII-b:C/flatset/col/7/1/1/2/4/2/4/1`)

Source `the November 2 reference manuscript` 1650-1656, 1684-1689, 3426-3430.

Applies `sfcDuhamelEverywhere_of` to `sfcCausalHeatCont` (`_1`), `sfcCausalHeatPer` (`_2`) and
`ageμOpenPos` (`_3`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem sfcDuhamelEverywhere : SFCDuhamelEverywhere :=
  sfcDuhamelEverywhere_of sfcCausalHeatCont sfcCausalHeatPer ageμOpenPos

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
