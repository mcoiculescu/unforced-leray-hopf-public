import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Leaves
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_4
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_4.KcJointMeasurable
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_4.KcDivFree
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_4.KcGradient
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_4.EnergyLocOfSlice
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_4.ZeroEntranceOfSlice

/-!
# `KcPathEnergy` (task `PartIII-b:C/flatset/col/4`)

Source of record `the November 2 reference manuscript`: 3426-3430, 4614-4615.
Assembly of `kcPathEnergy_of` (`Sub/PartIII-b_C_flatset_col_4.lean`) with the five leaves
`kcJointMeasurable`, `kcDivFree`, `kcGradient`, `energyLocOfSlice`, `zeroEntranceOfSlice`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem kcPathEnergy : KcPathEnergy :=
  kcPathEnergy_of kcJointMeasurable kcDivFree kcGradient energyLocOfSlice zeroEntranceOfSlice

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
