import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T23_5_1_2
import UnforcedLeray.Short.PartIIIa.T23_StressExactSplit.T23_5.GaussTermBound
import UnforcedLeray.Short.PartIIIa.T23_StressExactSplit.T23_5.GaussLatticeSum

/-!
# Leaf-assembled `GaussianPeriodicDecay` (SP 2356-2358)

Assembles the two leaves `gaussTermBound` (one periodized Gaussian term) and `gaussLatticeSum`
(lattice Gaussian sums) through `gaussianPeriodicDecay_of`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIIa

/-- **Periodized Gaussian remainder decay** (SP 2356-2358), assembled from the two leaves. -/
theorem gaussianPeriodicDecay : UnforcedLeray.Short.IIIa.GaussianPeriodicDecay :=
  gaussianPeriodicDecay_of gaussTermBound gaussLatticeSum

end UnforcedLeray.Short.IIIa
