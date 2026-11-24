import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_1
import UnforcedLeray.Short.PartIIIa.Clock.FrameAmplitudeProof.ComplCoupling.HeatBound
import UnforcedLeray.Short.PartIIIa.Clock.FrameAmplitudeProof.ComplCoupling.EulerSubBound
import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.ShortBlock.PerturbDuhamel.WeakFlowDuhamel.FreeRateAssembly

/-!
# `PartIII-a:T21/c3/3/1`: `ShortComplPerturbDuhamel`

Source of record: `the November 2 reference manuscript` (SP), lines 2919-2925,
2937-2958, 2982-2988.

Assembles `shortComplPerturbDuhamel` from `shortComplPerturbDuhamel_of`, `movLamDualHeatBound`,
`movLamDualEulerSubBound`, and `weakFlowComplPerturbDuhamel_unconditional`.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.IIIa

theorem shortComplPerturbDuhamel (κ : UnforcedLeray.Short.IIIa.PlanarFrameKernels) :
    UnforcedLeray.Short.IIIa.ShortComplPerturbDuhamel κ :=
  UnforcedLeray.Short.IIIa.shortComplPerturbDuhamel_of κ
    (UnforcedLeray.Short.IIIa.movLamDualHeatBound κ)
    (_root_.movLamDualEulerSubBound κ)
    (UnforcedLeray.Short.IIIa.weakFlowComplPerturbDuhamel_unconditional κ)

end UnforcedLeray.Short.IIIa
