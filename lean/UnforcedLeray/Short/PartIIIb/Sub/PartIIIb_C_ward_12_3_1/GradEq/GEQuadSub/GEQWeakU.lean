import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_7_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_7_2.InletWeak
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_7_2.RepWeak
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_7_2.WeakSum

/-!
# `gEQWeakU` (source 2525-2531, 2385-2387)

Weak `y_j`-derivative of `u = e + rep w`, assembled from the three leaves `gEQInletWeak`,
`gEQRepWeak`, `gEQWeakSum` via `gEQWeakU_of`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem gEQWeakU : GEQWeakU := gEQWeakU_of gEQInletWeak gEQRepWeak gEQWeakSum

end UnforcedLeray.Short.PartIIIb.Concrete
