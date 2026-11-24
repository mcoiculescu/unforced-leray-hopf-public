import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_regime
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_2_3_3_1_L1
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_2_3_3_1_L2
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_2_3_3_1_L3_good
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_2_3_3_1_L4

/-!
# `PartIII-a:T21/c3/2/1/2/3/3/1`: `ComplMildTestedRegime`

Source of record: `the November 2 reference manuscript` (SP), lines 2861-2866,
2898-2925, 2937-2945, 2974-2982.

Assembles `complMildTestedRegime` from `complMildTestedRegime_of`, `complGeneratorSplitRegime_of`,
`aRelRoughReg`, and the three leaf theorems `movSolTestedDuhamelSmall`, `modeTestedDuhamelRegime`,
`movFrameLeavesRegime`.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.IIIa

theorem complMildTestedRegime (κ : UnforcedLeray.Short.IIIa.PlanarFrameKernels) :
    UnforcedLeray.Short.IIIa.ComplMildTestedSplit.Regime.ComplMildTestedRegime κ :=
  ComplMildTestedSplit.Regime.complMildTestedRegime_of κ
    _root_.movSolTestedDuhamelSmall
    (_root_.modeTestedDuhamelRegime κ)
    (ComplMildTestedSplit.Regime.complGeneratorSplitRegime_of κ
      (ComplMildTestedSplit.ARelRoughSub.aRelRoughReg κ)
      (_root_.movFrameLeavesRegime κ).1
      (_root_.movFrameLeavesRegime κ).2.1
      (_root_.movFrameLeavesRegime κ).2.2)

end UnforcedLeray.Short.IIIa
