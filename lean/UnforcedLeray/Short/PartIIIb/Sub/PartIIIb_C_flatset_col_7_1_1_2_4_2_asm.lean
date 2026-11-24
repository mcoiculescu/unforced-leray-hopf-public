import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_5
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_5.L1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_5.L2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_5.L3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_5.L4

/-!
# `sfcEnergyG_of`: `SFCEnergyG` from the four dependency lemmas
(decomposition of `PartIII-b:C/flatset/col/7/1/1/2/4/2/5`)

Source `the November 2 reference manuscript`
1684-1689, 3426-3430.  The four analytic Props of `sfcEnergyG_of_sub` are supplied by
`measRep_ex` (L1), `sliceHeat_bound` (L2), `gradIntegrand_aemeas` (L3), `cellWeightedL2` (L4).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem sfcEnergyG_of (hD : SFCDuhamel) (hH : SFCHeatGrad) (hP : SFCProjGrad)
    (hG : SFCDuhamelGrad) : SFCEnergyG :=
  sfcEnergyG_of_sub hD hH hP hG measRep_ex sliceHeat_bound gradIntegrand_aemeas cellWeightedL2

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
