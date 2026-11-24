import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1.LerayOf
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1.LerayRegKerIBP
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1.LerayRegApproxId
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1.LerayRegKerLimit

/-!
# Fundamental solution of the cylinder (`CylKerGreen`)

Source `the November 2 reference manuscript` 1676.  The identity
`∫_cell K_i Δh = -∂_i h(0)` is the assembly `cylKerGreen_of` of the three leaves
`regKerIBP`, `regApproxId`, `regKerLimit`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem cylKerGreen : CylKerGreen := cylKerGreen_of regKerIBP regApproxId regKerLimit

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
