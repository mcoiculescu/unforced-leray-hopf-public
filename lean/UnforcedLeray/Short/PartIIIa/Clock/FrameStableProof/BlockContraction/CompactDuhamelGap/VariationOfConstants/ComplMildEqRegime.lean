import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_regime
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_2_3_3_1_final

/-!
# `PartIII-a:T21/c3/2/1/2/3/3`: `ComplMildEqRegime`

Source of record: `the November 2 reference manuscript` (SP), lines 2836-2852,
2914-2925, 2937-2945.

Assembles `complMildEqRegime` from `complMildEqRegime_of_tested` and `complMildTestedRegime`.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.IIIa

theorem complMildEqRegime (κ : UnforcedLeray.Short.IIIa.PlanarFrameKernels) :
    UnforcedLeray.Short.IIIa.ComplMildTestedSplit.Regime.ComplMildEqRegime κ :=
  UnforcedLeray.Short.IIIa.ComplMildTestedSplit.Regime.complMildEqRegime_of_tested κ
    (complMildTestedRegime κ)

end UnforcedLeray.Short.IIIa
