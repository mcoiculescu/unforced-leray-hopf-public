import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_1
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.LocalizedSourceBounds
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.KernelAdjoint

/-!
# Part III-a, `PartIII-a:T21/2/1`: `adjointLocalizedBound`

Source of record: `the November 2 reference manuscript` (SP) lines 3052-3058.
The proof is the assembly `adjointLocalizedBound_of` of the kernel adjoint bound
`kernelAdjointBound` (T21/2/1/2) and the localized source bounds `localizedSourceBounds`
(T21/2/1/1), with `1 < m` from `8 < m`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- **Adjoint localized bound** (SP 3052-3058): from the rescaled train bounds, the adjoint
localized interaction maps `X_{-m,d}` to `H^1_{-m,d}` uniformly, for BUC trains. -/
theorem adjointLocalizedBound (m : ℝ) (hm : 8 < m) (hT : RescaledTrainBounds m) :
    AdjointLocalizedBound m :=
  adjointLocalizedBound_of m (by linarith) (kernelAdjointBound m) (localizedSourceBounds m hm hT)

end UnforcedLeray.Short.IIIa
