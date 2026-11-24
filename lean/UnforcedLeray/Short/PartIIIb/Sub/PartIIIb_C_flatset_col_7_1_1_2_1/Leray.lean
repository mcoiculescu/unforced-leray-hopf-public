import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1.LerayOf
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1.LerayDrivingOfSmooth
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1.LeraySolenoidal
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1.LerayGradPerp
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1.LerayMemLp
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1.LerayForceRep
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1.LerayFieldProps
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1.LerayPotSmooth
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1.LerayPotDecay

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- **Leray representative** (source 1655-1656, 1676): the flat Leray projection of a smooth force
has an `H_g`-density in the class `IsDriving`. Assembled from the leaves. -/
theorem lerayDriving : LerayDriving :=
  lerayDriving_of drivingOfSmooth smoothSolenoidal smoothGradPerp memLpOfDecay smoothForceRep
    lerayFieldProps lerayPotSmooth lerayPotDecay

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
