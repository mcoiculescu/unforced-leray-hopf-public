import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.BlockContraction.CompactDuhamelGap.VariationOfConstants.DuhamelAbstract
import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.BlockContraction.CompactDuhamelGap.VariationOfConstants.RelRegularity
import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.BlockContraction.CompactDuhamelGap.VariationOfConstants.ComplMild
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_regime

/-!
# `PartIII-a:T21/c3/2/1/2`: `ComplBlockDuhamelVoCReg`

Source of record: `the November 2 reference manuscript` (SP), lines 2919-2925,
2962-2982.

Assembles `complBlockDuhamelVoCReg` from `complBlockDuhamelVoCReg_of`,
`complBlockDuhamelSplitReg_of_mildRegime`, `duhamelVoCAbstract`, `relBlockRegularityReg`,
and `complMovingMildRegime`.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.IIIa

theorem complBlockDuhamelVoCReg (κ : UnforcedLeray.Short.IIIa.PlanarFrameKernels) :
    UnforcedLeray.Short.IIIa.VariationOfConstantsMildSub.ComplBlockDuhamelVoCReg κ :=
  UnforcedLeray.Short.IIIa.VariationOfConstantsMildSub.complBlockDuhamelVoCReg_of κ
    (UnforcedLeray.Short.IIIa.ComplMildTestedSplit.Regime.complBlockDuhamelSplitReg_of_mildRegime κ
      UnforcedLeray.Short.IIIa.duhamelVoCAbstract
      (relBlockRegularityReg κ)
      (complMovingMildRegime κ))

end UnforcedLeray.Short.IIIa
