import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_3_2_dec
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_3_2_3_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_3_2_3_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_3_2_3_3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_3_2_3_4

/-!
# `pepsC0SliceOrth` (task `PartIII-b:C/flatset/col/7/1/1/2/4/2/3/2/3`)

Source `the November 2 reference manuscript` 1650-1656, 1676.

Assembles the slice orthogonality from the four lemma theorems
`pepsC0SliceMemLp`, `pepsC0SliceDivFreeAE`, `pepsC0SliceOrthCell`, `pepsC0FubiniOrth`
via `pepsC0SliceOrth_of` (compiled in the dec file).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem pepsC0SliceOrth : PepsC0SliceOrth :=
  pepsC0SliceOrth_of pepsC0SliceMemLp pepsC0SliceDivFreeAE pepsC0SliceOrthCell pepsC0FubiniOrth

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
