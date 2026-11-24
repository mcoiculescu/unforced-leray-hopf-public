import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3
import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.FlowMeas
import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.BlockContraction
import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.ShortBlock

/-!
# `PartIII-a:T21/c3`: `FrameStableAll`

Source of record: `the November 2 reference manuscript` (SP), lines 2960-3006.

Assembles `frameStableAll` from `frameStableAll_of`, `frameFlowMeasurable`,
`frameBlockContraction`, and `frameShortBlockBound`.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.IIIa

theorem frameStableAll (κ : UnforcedLeray.Short.IIIa.PlanarFrameKernels)
    (h : UnforcedLeray.Short.IIIa.IsSeedKernels κ) :
    UnforcedLeray.Short.IIIa.FrameStableAll κ :=
  frameStableAll_of κ h (frameFlowMeasurable κ)
    (frameBlockContraction κ) (frameShortBlockBound κ)

end UnforcedLeray.Short.IIIa
