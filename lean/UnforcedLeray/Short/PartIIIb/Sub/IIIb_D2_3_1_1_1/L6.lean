import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_1

/-!
# `AgeWeightShift` (source 2666-2679)

The age weights of `H`, `H_T`: `s² · s^{-5/2} dς = s^{-1/2} dς` (`lintegral_ageμ` on both sides).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- **Age weights** (source 2666-2679): `s² · s^{-5/2} dς = s^{-1/2} dς`. -/
theorem ageWeightShift : AgeWeightShift := by
  intro c hc f hf
  have hmeas1 : Measurable (fun p : Chart => ENNReal.ofReal (p.1 ^ 2) * f p) :=
    ((measurable_fst.pow_const 2).ennreal_ofReal).mul hf
  rw [lintegral_ageμ hc (-5 / 2) hmeas1, lintegral_ageμ hc (-1 / 2) hf]
  refine setLIntegral_congr_fun
    (measurableSet_Ioi.prod (measurableSet_Ico.prod MeasurableSet.univ)) fun p hp => ?_
  have hp0 : 0 < p.1 := hp.1
  have h0 : 0 ≤ c⁻¹ * p.1 ^ (-5 / 2 : ℝ) :=
    mul_nonneg (inv_nonneg.2 hc.le) (Real.rpow_nonneg hp0.le _)
  have hpow : p.1 ^ (-5 / 2 : ℝ) * p.1 ^ 2 = p.1 ^ (-1 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hp0]
    norm_num
  rw [← mul_assoc, ← ENNReal.ofReal_mul h0, mul_assoc c⁻¹ (p.1 ^ (-5 / 2 : ℝ)) (p.1 ^ 2), hpow]

end UnforcedLeray.Short.PartIIIb.Concrete
