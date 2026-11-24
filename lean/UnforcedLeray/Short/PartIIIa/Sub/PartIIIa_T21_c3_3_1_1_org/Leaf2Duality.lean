import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_1_1_org.Leaf2Duality.Assembly
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_1_1_org.Leaf2Duality.FreeAdjExists
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_1_1_org.Leaf2Duality.FreeCylDuality
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_1_1_org.Leaf2Duality.CylDataDense

/-!
# `PartIII-a:T21/c3/3/1/1/2/2/2`: `FreeMovingDuality`

Source of record: `the November 2 reference manuscript` (SP), lines 2937-2958.

Assembles `freeMovingDuality` from `freeMovingDuality_of` and the three leaf theorems
`FreeAdjExists`, `FreeCylDuality`, `CylDataDense`.
-/

set_option autoImplicit false

namespace UnforcedLeray.Short.IIIa.ComplFreeRateSub

theorem freeMovingDuality (ν m : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    (t₁ t₂ : ℝ) : UnforcedLeray.Short.IIIa.ComplFreeRateSub.FreeMovingDuality ν m tr t₁ t₂ :=
  freeMovingDuality_of ν m tr t₁ t₂
    (_root_.freeAdjExists ν m tr t₁ t₂)
    (Leaf2DualityNeeded.freeCylDuality ν m tr t₁ t₂)
    Leaf2DualityNeeded.cylDataDense

end UnforcedLeray.Short.IIIa.ComplFreeRateSub
