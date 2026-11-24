import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_proj2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_3_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_3_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_3_3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_3_4
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_3_5

/-!
# `SFCProjGrad` (drafting task `PartIII-b:C/flatset/col/7/1/1/2/4/2/3`, theorem `sfcProjGrad`)

Source `the November 2 reference manuscript` 1650-1656, 1684-1689, 3426-3430.

Composition: `sfcProjGrad_of` applied to `sfcLiftForce` (`/3/1`), `pepsC0Slices` (`/3/2`),
`p0SmoothFamily` (`/3/3`), `p0GradContract` (`/3/4`) and `smoothForceGradBound` (`/3/5`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem sfcProjGrad : SFCProjGrad :=
  sfcProjGrad_of sfcLiftForce pepsC0Slices p0SmoothFamily p0GradContract smoothForceGradBound

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
