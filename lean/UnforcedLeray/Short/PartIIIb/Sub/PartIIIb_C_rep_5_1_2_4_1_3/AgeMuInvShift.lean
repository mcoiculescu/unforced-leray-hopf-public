import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_2_4_1_3.Kernel
import UnforcedLeray.Lib.AxisymmetricB.Lift

/-!
# `PartIII-b:C/rep/5/1/2/4/1/3/3/8`: the age weight `s⁻¹ · s^{-3/2} = s^{-5/2}`

Source `the November 2 reference manuscript` 2679-2684.  On the half cell
`(0, ∞) × qCell c`, the integrand `c⁻¹ s^{-3/2}` against `ageμ c (-3/2)` times `s⁻¹` equals
`c⁻¹ s^{-5/2}`, the density of `ageμ c (-5/2)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete.WYCore

/-- **Age weights** (source 2679-2684): `s⁻¹ · s^{-3/2} dς = s^{-5/2} dς`. -/
theorem ageμInvShift : AgeμInvShift := by
  intro c hc f hf
  have hm : Measurable fun p : ℝ × (ℝ × ℝ) => ENNReal.ofReal (p.1⁻¹) * f p :=
    (ENNReal.measurable_ofReal.comp (measurable_fst.inv)).mul hf
  rw [lintegral_ageμ hc (-3 / 2) hm, lintegral_ageμ hc (-5 / 2) hf]
  refine setLIntegral_congr_fun
    (measurableSet_Ioi.prod (measurableSet_Ico.prod MeasurableSet.univ)) fun p hp => ?_
  have hs : 0 < p.1 := hp.1
  rw [← mul_assoc, ← ENNReal.ofReal_mul
    (mul_nonneg (inv_nonneg.2 hc.le) (Real.rpow_nonneg hs.le _))]
  congr 2
  rw [show (-5 / 2 : ℝ) = -3 / 2 + -1 by norm_num, Real.rpow_add hs, Real.rpow_neg_one]
  ring

end UnforcedLeray.Short.PartIIIb.Concrete.WYCore

end
