import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3
import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.ShortBlock.PerturbDuhamel
import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.ShortBlock.OscillatorForce
import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.ShortBlock.EulerError

/-!
# `PartIII-a:T21/c3/3`: `FrameShortBlockBound`

Source of record: `the November 2 reference manuscript` (SP), lines 2898-2962,
2982-2988.

Assembles `frameShortBlockBound` from `frameShortBlockBound_of`, `shortComplPerturbDuhamel`,
`complModeForceOscillator`, and `complModeForceEulerError`.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.IIIa

theorem frameShortBlockBound (κ : UnforcedLeray.Short.IIIa.PlanarFrameKernels) :
    UnforcedLeray.Short.IIIa.FrameShortBlockBound κ :=
  frameShortBlockBound_of κ (shortComplPerturbDuhamel κ)
    (complModeForceOscillator κ) (complModeForceEulerError κ)

end UnforcedLeray.Short.IIIa
