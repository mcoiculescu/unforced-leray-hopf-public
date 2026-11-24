import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_2_6.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_2_6.HedbergPtwise
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_2_6.HLMaxL2
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.StreamPotOrg.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_2_6.HLMaxMeasurable
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-!
# Scalar `L² → L⁶` bound for the Biot-Savart potential

Source `the November 2 reference manuscript`: stream potential of the solenoidal
cutoff, `L² * |w|⁻² → L⁶`. From Hedberg's pointwise bound `T G ≤ 2 (M G)^{1/3} (∫G²)^{1/3}`
(`hedbergPtwise`) we get `(T G)⁶ ≤ 64 (∫G²)² (M G)²` pointwise; integrating and using the
strong `(2,2)` bound `∫ (M G)² ≤ 1000 ∫ G²` (`hlMaxL2`) gives `∫ (T G)⁶ ≤ 64000 (∫G²)³`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Power identity: `((x)^{1/3})^6 = x^2` in `ℝ≥0∞`. -/
lemma rpow_third_six (x : ℝ≥0∞) : (x ^ (1 / 3 : ℝ)) ^ 6 = x ^ 2 := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, ← ENNReal.rpow_natCast]
  norm_num

/-- Pointwise sixth-power bound from Hedberg's bound. -/
lemma rieszT_six_le (G : Space → ℝ≥0∞) (hG : Measurable G) (y : Space) :
    (rieszT G y) ^ 6 ≤ (64 * (∫⁻ z, (G z) ^ 2) ^ 2) * (hlMax G y) ^ 2 := by
  have h := hedbergPtwise G hG y
  calc (rieszT G y) ^ 6
      ≤ (2 * (hlMax G y) ^ (1 / 3 : ℝ) * (∫⁻ z, (G z) ^ 2) ^ (1 / 3 : ℝ)) ^ 6 :=
        pow_le_pow_left' h 6
    _ = (64 * (∫⁻ z, (G z) ^ 2) ^ 2) * (hlMax G y) ^ 2 := by
        rw [mul_pow, mul_pow, rpow_third_six, rpow_third_six]
        ring

theorem rieszL6 : RieszL6 := by
  unfold RieszL6
  intro G hG
  have hM : Measurable (hlMax G) := hlMaxMeasurable G hG
  calc ∫⁻ y, (rieszT G y) ^ 6
      ≤ ∫⁻ y, (64 * (∫⁻ z, (G z) ^ 2) ^ 2) * (hlMax G y) ^ 2 :=
        lintegral_mono (fun y => rieszT_six_le G hG y)
    _ = (64 * (∫⁻ z, (G z) ^ 2) ^ 2) * ∫⁻ y, (hlMax G y) ^ 2 :=
        lintegral_const_mul _ (hM.pow_const 2)
    _ ≤ (64 * (∫⁻ z, (G z) ^ 2) ^ 2) * (1000 * ∫⁻ z, (G z) ^ 2) :=
        by gcongr; exact hlMaxL2 G hG
    _ = 64000 * (∫⁻ z, (G z) ^ 2) ^ 3 := by ring

end UnforcedLeray.Short.PartIIIb.Concrete
