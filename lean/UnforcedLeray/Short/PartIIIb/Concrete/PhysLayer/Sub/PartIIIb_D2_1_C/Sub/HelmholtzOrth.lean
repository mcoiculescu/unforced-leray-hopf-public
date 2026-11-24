import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.PartIIIb_IIIb_D2_1_3_1_2_2_4_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_3_1_5.Final

/-!
# `HelmholtzOrth` from `LerayDensityL2`

Source `the November 2 reference manuscript` 1351-1362, 1470-1480: a weakly
solenoidal `h ∈ Y_2` orthogonal to solenoidal phase tests is weakly harmonic (curl curl identity)
and hence zero (Weyl in `L²`); this is `lerayDensityL2` (Sub `…_1_3_1_2_1_3_1_5/Final`).
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem helmholtzOrth : HelmholtzOrth := fun P hP _ h hh hsol hann Ψ hΨ =>
  lerayDensityL2 P hP h hh hsol hann Ψ hΨ

end UnforcedLeray.Short.PartIIIb.Concrete
