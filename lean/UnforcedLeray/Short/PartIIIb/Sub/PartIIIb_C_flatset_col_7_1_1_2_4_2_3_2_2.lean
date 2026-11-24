import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_3_2_dec
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_3_2_2_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_3_2_2_2

/-!
# `pepsC0SliceSolenoidal` (task `PartIII-b:C/flatset/col/7/1/1/2/4/2/3/2/2`)

Source `the November 2 reference manuscript` 1650-1656, 1676.

Assembly: `pepsC0SliceSolenoidal_of` (in the `_dec` file) reduces solenoidality of `Ψ` to the two
slice-wise facts `PepsC0FubiniSol` (task `/2/2/1`) and `PepsC0SliceDivFreeZero` (task `/2/2/2`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem pepsC0SliceSolenoidal : PepsC0SliceSolenoidal :=
  pepsC0SliceSolenoidal_of pepsC0FubiniSol pepsC0SliceDivFreeZero

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
