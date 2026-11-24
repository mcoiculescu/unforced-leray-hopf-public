import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_3_2_of
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_3_2_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_3_2_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_3_2_3

/-!
# `PepsC0Slices` (task `PartIII-b:C/flatset/col/7/1/1/2/4/2/3/2`)

Source `the November 2 reference manuscript` 1650-1656, 1676.

Unconditional assembly: `pepsC0Slices_of` (in the `_of` file) applied to the three slice-wise
facts `pepsC0SliceL2` (`_1`), `pepsC0SliceSolenoidal` (`_2`) and `pepsC0SliceOrth` (`_3`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem pepsC0Slices : PepsC0Slices :=
  pepsC0Slices_of pepsC0SliceL2 pepsC0SliceSolenoidal pepsC0SliceOrth

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
