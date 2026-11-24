import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6_3_3_4
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6_3_3_4.VtvEtaJet
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6_3_3_4.VtvFlowCyl
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6_3_3_4.VtvFlowJet
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_6_3_3_4.VtvEcJet

/-!
# `vtvTestBounds`: the four leaves assembled (source 270-288, 4610)

Assembles `vtvTestBounds_of` from the leaves `vtvEtaJet`, `vtvFlowCyl`, `vtvFlowJet`, `vtvEcJet`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem vtvTestBounds : VtvTestBounds :=
  vtvTestBounds_of vtvEtaJet vtvFlowCyl vtvFlowJet vtvEcJet

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

end
