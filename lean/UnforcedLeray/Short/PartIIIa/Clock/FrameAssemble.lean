import UnforcedLeray.Short.PartIIIa.Clock.Frame
import UnforcedLeray.Short.PartIIIa.Clock.FrameKernels
import UnforcedLeray.Short.PartIIIa.Clock.FrameFacts
import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof
import UnforcedLeray.Short.PartIIIa.Clock.FrameAmplitudeProof

/-!
# `PartIII-a:T21/frame`: `GoodFrameExists`

Source of record: `the November 2 reference manuscript`.

Assembles `goodFrameExists` from `goodFrameExists_of_leaves`, `planarFrameKernelsExist`,
`perFrameFactsAll`, `frameStableAll`, and `frameAmplitudeAll`.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.IIIa

theorem goodFrameExists : UnforcedLeray.Short.IIIa.GoodFrameExists :=
  goodFrameExists_of_leaves
    planarFrameKernelsExist
    (fun κ h => perFrameFactsAll κ h)
    (fun κ h => frameStableAll κ h)
    (fun κ h => _root_.frameAmplitudeAll κ h)

end UnforcedLeray.Short.IIIa
