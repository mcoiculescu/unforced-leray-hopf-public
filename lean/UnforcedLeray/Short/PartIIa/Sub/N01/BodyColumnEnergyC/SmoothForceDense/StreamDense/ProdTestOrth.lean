import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_9_1_1_3_2
import UnforcedLeray.Short.PartIIa.Sub.N01.BodyColumnEnergyC.SmoothForceDense.StreamDense.ProdTestOrth.DivPairing
import UnforcedLeray.Short.PartIIa.Sub.N01.BodyColumnEnergyC.SmoothForceDense.StreamDense.ProdTestOrth.CurlPairing
import UnforcedLeray.Short.PartIIa.Sub.N01.BodyColumnEnergyC.SmoothForceDense.StreamDense.ProdTestOrth.SliceLocInt

/-!
# `prodTestOrth` (`PartII-a:N01/9/1/1/3/2`), source lines 1684-1689

The product tests `θ(s) ψ(q,η)` are orthogonal to the solenoidal complement, by
`prodTestOrth_of` applied to `divPairing`, `curlPairing` and `sliceLocInt`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIa.N01.Sub

theorem prodTestOrth : UnforcedLeray.Short.PartIIa.N01.Sub.ProdTestOrth :=
  prodTestOrth_of divPairing curlPairing sliceLocInt

end UnforcedLeray.Short.PartIIa.N01.Sub
