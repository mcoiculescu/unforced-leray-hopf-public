import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_asm
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_duh
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_heat
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_proj
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_dgrad

/-!
# `sfcEnergyG`: `SFCEnergyG` from the four lemma theorems and `sfcEnergyG_of`
(decomposition of `PartIII-b:C/flatset/col/7/1/1/2/4/2`)

Source `the November 2 reference manuscript` 1650-1656, 1684-1689, 3426-3430.
Immediate composition of `sfcEnergyG_of` (`_asm.lean`) with `sfcDuhamel` (`_duh.lean`),
`sfcHeatGrad` (`_heat.lean`), `sfcProjGrad` (`_proj.lean`) and `sfcDuhamelGrad` (`_dgrad.lean`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem sfcEnergyG : SFCEnergyG :=
  sfcEnergyG_of sfcDuhamel sfcHeatGrad sfcProjGrad sfcDuhamelGrad

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
