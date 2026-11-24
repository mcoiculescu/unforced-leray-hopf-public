import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.PointDom.Sub.PartIIIb_C_rep_5_1_2_4_1_2_7
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.PointDom.Sub.PartIIIb_C_rep_5_1_2_4_1_2_7_1
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.PointDom.Sub.PartIIIb_C_rep_5_1_2_4_1_2_7_2

/-!
# `PDX0Rep` (`PartIII-b:C/rep/5/1/2/4/1/2/7`)

Assembles the two leaves `pdX0RepIntegrable` (`…/2/7/1`) and `pdX0RepCoV` (`…/2/7/2`)
through the reduction `pdX0Rep_of` (`…/2/7`). Source `the November 2 reference manuscript`
3611-3617 (`sep:resolvent`), 4171.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem pdX0Rep : PDX0Rep := pdX0Rep_of pdX0RepIntegrable pdX0RepCoV

end UnforcedLeray.Short.PartIIIb.Concrete

end
