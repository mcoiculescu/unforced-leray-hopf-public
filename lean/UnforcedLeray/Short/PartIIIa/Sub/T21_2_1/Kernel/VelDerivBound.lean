import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_1_2_11
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.Kernel.VelDerivLeray

/-!


Source: `the November 2 reference manuscript` (lines 3056-3057, 2254-2259), via
the assembly `kerVelDerivBound_of_parts` of `Sub/PartIIIa_T21_2_1_2_11.lean` and the Leray field
`kerVelDerivLeray` of `Kernel/VelDerivLeray.lean`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIIa

theorem kerVelDerivBound_of (hFar : UnforcedLeray.Short.IIIa.KerVelFarField)
    (hD : UnforcedLeray.Short.IIIa.KerVelDivFree) (hC : UnforcedLeray.Short.IIIa.KerVelCurl)
    (hU : UnforcedLeray.Short.IIIa.KernelBiotSavartUnique) :
    UnforcedLeray.Short.IIIa.KerVelDerivBound :=
  kerVelDerivBound_of_parts hFar hD hC hU kerVelDerivLeray

end UnforcedLeray.Short.IIIa
