import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_6
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_6.ChiUnique
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_6.Weights
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_3_6.PhiMemLp

namespace UnforcedLeray.Short.IIIa.AdjE1

theorem adjChiDerivBound (m : ℝ) (hm : 8 < m) (hL : UnforcedLeray.Short.IIIa.AdjointLocalizedBound m) : UnforcedLeray.Short.IIIa.AdjE1.AdjChiDerivBound m :=
  adjChiDerivBound_of m hL (adjChiUnique m) (adjChiWeights m) (adjPhiMemLp m)

end UnforcedLeray.Short.IIIa.AdjE1
