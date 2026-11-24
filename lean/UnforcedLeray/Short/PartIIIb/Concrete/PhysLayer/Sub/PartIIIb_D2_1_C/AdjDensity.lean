import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjDensityOf
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTrunc
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjMoll
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.PhaseLpTri2

/-!
# `fwuAdjDensity`: density of the solenoidal phase tests in the adjoint domain

Assembly of the three ingredients `fwuAdjTrunc` (`AdjTrunc.lean`), `fwuAdjMoll` (`AdjMoll.lean`)
and `phaseLpTri2` (`PhaseLpTri2.lean`) through `fwuAdjDensity_of` (`AdjDensityOf.lean`).
Source: `the November 2 reference manuscript` lines 1351-1362, 1556-1583.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem fwuAdjDensity : FWUAdjDensity :=
  fwuAdjDensity_of fwuAdjTrunc fwuAdjMoll phaseLpTri2

end UnforcedLeray.Short.PartIIIb.Concrete
