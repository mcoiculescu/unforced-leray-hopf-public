import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_7_3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_7_2.InletWeak
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_7_2.RepWeak
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_7_2.WeakSum

/-!
# `gEQWeakDu` (source 2525-2531)

Weak `y_k`-derivative of `D_j u`, assembled from the three leaves `gEQInletWeak`,
`gEQRepWeak`, `gEQWeakSum` via `gEQWeakDu_of`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem gEQWeakDu : GEQWeakDu := gEQWeakDu_of gEQInletWeak gEQRepWeak gEQWeakSum

end UnforcedLeray.Short.PartIIIb.Concrete
