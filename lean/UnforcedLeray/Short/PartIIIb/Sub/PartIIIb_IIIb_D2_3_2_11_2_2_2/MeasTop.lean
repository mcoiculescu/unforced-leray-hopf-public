import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_3_2_11_2_2_2_3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_3_2_11_2_2_2_3.L1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_3_2_11_2_2_2_3.L2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_3_2_11_2_2_2_3.L3

/-!
# `SepPhiMeasurableTop` (`PartIII-b:IIIb-D2/3/2/11/2/2/2/3/3`, source 3604-3621)

Discharges the measurability source fact by the joint-smoothness chain
`heatLerayKJointSmoothTop` (L1) → `sepKernelFactorJointSmooth_of` (L2) →
`sepPhiJointSmoothTop_of` (L3) → `sepPhiMeasurableTop_of` (sub-file).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- `SepPhiMeasurableTop` holds: the integrand is jointly smooth on `l ∈ (0,1)`, so its
`x`-derivatives of every order are continuous in `p` on the full-measure set `(0,1) × ℝ³`. -/
theorem sepPhiMeasurableTop : SepPhiMeasurableTop :=
  sepPhiMeasurableTop_of (sepPhiJointSmoothTop_of (sepKernelFactorJointSmooth_of heatLerayKJointSmoothTop))

end UnforcedLeray.Short.PartIIIb.Concrete
