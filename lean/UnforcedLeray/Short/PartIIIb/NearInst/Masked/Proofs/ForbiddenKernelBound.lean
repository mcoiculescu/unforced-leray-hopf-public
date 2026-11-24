import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.PositiveKernel
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.PositiveKernel.FarPointwise
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.PositiveKernel.FarMajorantL2

/-!
# `forbiddenKernelBound_of`: the forbidden separated subblock kernel estimate (source 4011-4014)

From the pointwise majorant `farPointwiseMajorant_of` (source 3611-3621, 3604-3610) and the
`L²` bound of the positive majorant `farMajorantL2_holds` (source 3996-4005), the assembly
`forbiddenKernelBound_of_sub` gives `ForbiddenKernelBound`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

/-- The forbidden separated subblock kernel estimate (source 4011-4014), from `SepKernelBounds`. -/
theorem forbiddenKernelBound_of (hK : UnforcedLeray.Short.IIIa.SepKernelBounds) :
    ForbiddenKernelBound :=
  forbiddenKernelBound_of_sub (farPointwiseMajorant_of hK) farMajorantL2_holds

end UnforcedLeray.Short.PartIIIb.NearInst.Masked
