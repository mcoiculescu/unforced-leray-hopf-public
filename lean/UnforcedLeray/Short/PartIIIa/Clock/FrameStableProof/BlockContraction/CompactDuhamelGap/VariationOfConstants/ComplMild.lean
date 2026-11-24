import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.BlockContraction.CompactDuhamelGap.VariationOfConstants.ComplMildY
import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.BlockContraction.CompactDuhamelGap.VariationOfConstants.ComplMildG
import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.BlockContraction.CompactDuhamelGap.VariationOfConstants.ComplMildEqRegime
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_regime

/-!
# `PartIII-a:T21/c3/2/1/2/3`: `ComplMovingMildRegime`

Source of record: `the November 2 reference manuscript` (SP), lines 2836-2852,
2914-2925, 2974-2982.

Assembles `complMovingMildRegime` from `complMovingMildRegime_of`, `complYExists`,
`complGExists`, and `complMildEqRegime`.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.IIIa

theorem complMovingMildRegime (κ : UnforcedLeray.Short.IIIa.PlanarFrameKernels) :
    UnforcedLeray.Short.IIIa.ComplMildTestedSplit.Regime.ComplMovingMildRegime κ :=
  UnforcedLeray.Short.IIIa.ComplMildTestedSplit.Regime.complMovingMildRegime_of κ
    (UnforcedLeray.Short.IIIa.complYExists κ)
    (UnforcedLeray.Short.IIIa.complGExists κ)
    (complMildEqRegime κ)

end UnforcedLeray.Short.IIIa
