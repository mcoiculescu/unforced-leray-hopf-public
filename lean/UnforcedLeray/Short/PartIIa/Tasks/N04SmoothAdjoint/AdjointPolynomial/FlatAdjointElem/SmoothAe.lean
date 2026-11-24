import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N04_2_2_1
import UnforcedLeray.Short.PartIIa.Tasks.N04SmoothAdjoint.AdjointPolynomial.FlatAdjointElem.SmoothAe.Smooth
import UnforcedLeray.Short.PartIIa.Tasks.N04SmoothAdjoint.AdjointPolynomial.FlatAdjointElem.SmoothAe.Ae

/-!


Assembles `flatAdjointSmoothAe` from `N04_2_2_1.flatAdjointSmoothAe_of`,
`N04_2_2_1.flatAdjointSmoothProp`, and `N04_2_2_1.flatAdjointAeProp`.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartIIa

theorem flatAdjointSmoothAe : FlatAdjointSmoothAe :=
  N04_2_2_1.flatAdjointSmoothAe_of
    N04_2_2_1.flatAdjointSmoothProp
    N04_2_2_1.flatAdjointAeProp

end UnforcedLeray.Short.PartIIa
