import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.AdjWeakSmooth
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.AdjRateCont
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.AdjDtDeriv
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.AdjIBP
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.AdjInt

/-!
# Part III-a: the classical adjoint equation for jointly smooth weak solutions (`adjWeakPointwise`)

Source of record: `the November 2 reference manuscript` (SP), lines 3052-3060.
The four leaves `adjWRateCont`, `adjWDtDeriv`, `adjWIBP`, `adjWInt` are proved in
`Sub/T21_2_3/LinAdjDuality/`; `adjWeakPointwise_of` (in `AdjWeakSmooth`) assembles them.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.IIIa

/-- **The classical adjoint equation for a jointly smooth weak solution** (SP 3060): assembled from
the four leaves. -/
theorem adjWeakPointwise (m : ℝ) : UnforcedLeray.Short.IIIa.AdjWeakPointwise m :=
  adjWeakPointwise_of m (adjWRateCont m) (adjWDtDeriv m) (adjWIBP m) (adjWInt m)

end UnforcedLeray.Short.IIIa
