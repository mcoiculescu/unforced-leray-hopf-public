import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_E
import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.BlockContraction.CompactDuhamelGap.BlockPropagator
import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.BlockContraction.CompactDuhamelGap.VariationOfConstants

/-!
# `PartIII-a:T21/c3/2/1`: `BlockCompactDuhamelGapE`

Source of record: `the November 2 reference manuscript` (SP), lines 2919-2928,
2962-2982.

Assembles `blockCompactDuhamelGapE` from `blockCompactDuhamelGapRegE_of`,
`dampedComplBlockPropagatorE`, and `complBlockDuhamelVoCReg`.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.IIIa

theorem blockCompactDuhamelGapE (κ : UnforcedLeray.Short.IIIa.PlanarFrameKernels) :
    UnforcedLeray.Short.IIIa.BlockCompactDuhamelGapE κ :=
  blockCompactDuhamelGapRegE_of κ (dampedComplBlockPropagatorE κ) (complBlockDuhamelVoCReg κ)

end UnforcedLeray.Short.IIIa
