import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1_of
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1.Leray
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1.Bridge
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1.Smooth
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1.Periodic
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1.SliceBound

/-!
# `SFCRep` (`PartIII-b:C/flatset/col/7/1/1/2/1`)

Source `the November 2 reference manuscript` 1650-1656, 1684-1689.
Instantiates `sfcRep_of` with the five Duhamel facts `lerayDriving`, `duhamelBridge`,
`duhamelSmooth`, `duhamelPeriodic`, `duhamelSliceBound` proved in the leaf files.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem sfcRep : SFCRep :=
  sfcRep_of lerayDriving duhamelBridge duhamelSmooth duhamelPeriodic duhamelSliceBound

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
