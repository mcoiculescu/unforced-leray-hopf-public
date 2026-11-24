import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_2_3_1
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_2_3_1.L2

/-!
# Kernel equivariance (`PartIII-b:IIIb-D2/3/1/2/3/1`)

Source of record: `the November 2 reference manuscript` lines 3600-3610
(`K_t = δG_t + ∂∂∫_t^∞ G`, radial dependence). The proof composes the reduction
`kernelEquivariance_of` (Sub file `IIIb-D2_3_1_2_3_1`) with the `C²` regularity
`heatTailC2Pos` of the heat tail for positive time (`IIIb-D2_3_1_2_3_1/L2`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **Kernel equivariance** (`PartIII-b:IIIb-D2/3/1/2/3/1`): `K_t(Mx) = M K_t(x) Mᵀ` for every
orthogonal `M`, every real `t` and every `x`. -/
theorem kernelEquivariance : KernelEquivariance := kernelEquivariance_of heatTailC2Pos

end UnforcedLeray.Short.PartIIIb.Concrete
