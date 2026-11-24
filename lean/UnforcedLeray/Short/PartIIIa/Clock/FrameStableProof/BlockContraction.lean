import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_E
import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.BlockContraction.CompactDuhamelGap
import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.ShortBlock.OscillatorForce
import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.ShortBlock.EulerError

/-!
# `PartIII-a:T21/c3/2`: `FrameBlockContraction`

Source of record: `the November 2 reference manuscript` (SP), lines 2898-2982.

Assembles `frameBlockContraction` from `frameBlockContraction_ofE`,
`blockCompactDuhamelGapE`, `complModeForceOscillator`, and `complModeForceEulerError`.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.IIIa

theorem frameBlockContraction (κ : UnforcedLeray.Short.IIIa.PlanarFrameKernels) :
    UnforcedLeray.Short.IIIa.FrameBlockContraction κ :=
  frameBlockContraction_ofE κ (blockCompactDuhamelGapE κ)
    (complModeForceOscillator κ) (complModeForceEulerError κ)

end UnforcedLeray.Short.IIIa
