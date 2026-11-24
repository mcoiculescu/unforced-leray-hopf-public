import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N04_2_2
import UnforcedLeray.Short.PartIIa.Tasks.N04SmoothAdjoint.AdjointPolynomial.FlatAdjointElem.SmoothAe
import UnforcedLeray.Short.PartIIa.Tasks.N04SmoothAdjoint.AdjointPolynomial.FlatAdjointElem.Gen1Bound
import UnforcedLeray.Short.PartIIa.Tasks.N04SmoothAdjoint.AdjointPolynomial.FlatAdjointElem.Gen2Bound

/-!


Assembles `flatAdjointElementaryBound` from `flatAdjointElementaryBound_of`,
`flatAdjointSmoothAe`, `flatAdjointGen1Bound`, and `flatAdjointGen2Bound`.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.PartIIa

theorem flatAdjointElementaryBound : FlatAdjointElementaryBound :=
  flatAdjointElementaryBound_of
    flatAdjointSmoothAe
    flatAdjointGen1Bound
    flatAdjointGen2Bound

end UnforcedLeray.Short.PartIIa
