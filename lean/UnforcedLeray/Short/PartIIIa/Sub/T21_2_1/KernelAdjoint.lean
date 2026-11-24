import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_1
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.KernelAdjointOf
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.NearFar
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.AdjSplit
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.XNormSplit
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.AdjFubini
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.DivPointwise
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.CurlPointwise
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.VelFarField
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.VelDivFree
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.VelCurl
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.Unique
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.VelDerivBound
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.WeakDerivRiesz

/-!
# Part III-a, `PartIII-a:T21/2/1/2`: `KernelAdjointBound` (assembly of the kernel leaves)

Source of record: `the November 2 reference manuscript` (SP) lines 3052-3057
and 2875-2896. The proof is the term assembly of the twelve kernel leaves through
`kernelAdjointBound_of` (`KernelAdjointOf.lean`); no new analysis.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.IIIa

/-- **`KernelAdjointBound`** (SP 2875-2896, 3052-3057): assembly of the kernel leaves. -/
theorem kernelAdjointBound (m : ℝ) : UnforcedLeray.Short.IIIa.KernelAdjointBound m := by
  have hNF : KerNearFar := kerNearFar
  have hFub : KerAdjFubini := kerAdjFubini_of hNF
  have hFar : KerVelFarField := kerVelFarField_of hNF
  have hD : KerVelDivFree := kerVelDivFree_of hFub (kerDivPointwise_of hNF)
  have hC : KerVelCurl := kerVelCurl_of hFub (kerCurlPointwise_of hNF)
  exact kernelAdjointBound_of m (kerAdjSplit_of hNF) (xNormSplitLe m)
    (kerVelDerivBound_of hFar hD hC kernelBiotSavartUnique) weakDerivOfBoundedPairing
    hFub hFar hD hC kernelBiotSavartUnique

end UnforcedLeray.Short.IIIa
