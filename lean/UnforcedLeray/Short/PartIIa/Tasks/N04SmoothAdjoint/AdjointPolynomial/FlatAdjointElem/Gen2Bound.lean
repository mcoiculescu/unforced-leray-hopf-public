import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N04_2_2_3
import UnforcedLeray.Short.PartIIa.Tasks.N04SmoothAdjoint.AdjointPolynomial.FlatAdjointElem.Gen2Bound.PairA
import UnforcedLeray.Short.PartIIa.Tasks.N04SmoothAdjoint.AdjointPolynomial.FlatAdjointElem.Gen2Bound.PairB
import UnforcedLeray.Short.PartIIa.Tasks.N04SmoothAdjoint.AdjointPolynomial.FlatAdjointElem.Gen2Bound.PairC

/-!


Assembles the three pair bounds (`flatAdjointGen2PairA`, `flatAdjointGen2PairB`,
`flatAdjointGen2PairC`) through `N04_2_2_3.flatAdjointGen2Bound_of`.
Source: `shorter-proof-2026-11-02.tex` lines 1814-1835.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIa

theorem flatAdjointGen2Bound : FlatAdjointGen2Bound :=
  N04_2_2_3.flatAdjointGen2Bound_of flatAdjointGen2PairA flatAdjointGen2PairB flatAdjointGen2PairC

end UnforcedLeray.Short.PartIIa

end
