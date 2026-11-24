import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.PartIIIb_IIIb_D2_1_3_1_2_2_4_1
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.AdjIntParts
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.HelmholtzOrth

/-!
# `adjFullEquation : AdjFullEquation`

Source `the November 2 reference manuscript` lines 1351-1362 and 1556-1583.
Assembles `AdjFullEquation` from the integration-by-parts part `adjIntParts`
(`AdjIntParts.lean`) and the Helmholtz orthogonality `helmholtzOrth` (`HelmholtzOrth.lean`)
via `adjFullEquation_of`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem adjFullEquation : AdjFullEquation :=
  adjFullEquation_of adjIntParts helmholtzOrth

end UnforcedLeray.Short.PartIIIb.Concrete
