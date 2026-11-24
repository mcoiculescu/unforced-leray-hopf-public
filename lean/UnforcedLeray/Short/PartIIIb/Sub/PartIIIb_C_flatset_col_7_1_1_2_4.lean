import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_of
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2

/-!
# `SFCEnergy` from the velocity half and the gradient half
(decomposition of `PartIII-b:C/flatset/col/7/1/1/2/4`)

Source `the November 2 reference manuscript` 1684-1689, 3426-3430.
Composition of `sfcEnergy_of` (`_of.lean`) with `sfcEnergyV` (`_1.lean`) and `sfcEnergyG` (`_2.lean`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem sfcEnergy : SFCEnergy :=
  sfcEnergy_of sfcEnergyV sfcEnergyG

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
