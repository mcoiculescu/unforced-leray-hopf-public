import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Exponent bookkeeping for `RepFarBox`

With `R > 0`, `e > 0`, `S > 0`: `R⁻¹ · (e R/√S)^{-23/11} = (R⁻¹)^{34/11} e^{-23/11} S^{23/22}`
(source 3631-3664, 5601-5605: `R⁻¹ D^{-23/11}` with `D = (1-e^{-δ/2})R/√S`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete.RepFarBoxIdent

theorem dm_identity (R e S : ℝ) (hR : 0 < R) (he : 0 < e) (hS : 0 < S) :
    R⁻¹ * (e * R / Real.sqrt S) ^ (-(23 / 11) : ℝ) =
      (R⁻¹) ^ (34 / 11 : ℝ) * e ^ (-(23 / 11) : ℝ) * S ^ (23 / 22 : ℝ) := by
  have hsq : 0 < Real.sqrt S := Real.sqrt_pos.2 hS
  rw [Real.div_rpow (by positivity) hsq.le, Real.mul_rpow he.le hR.le, Real.sqrt_eq_rpow,
    ← Real.rpow_mul hS.le, Real.inv_rpow hR.le]
  have hS' : S ^ ((1 / 2 : ℝ) * (-(23 / 11) : ℝ)) = (S ^ (23 / 22 : ℝ))⁻¹ := by
    rw [← Real.rpow_neg hS.le]; norm_num
  rw [hS', Real.rpow_neg hR.le]
  have h34 : R ^ (34 / 11 : ℝ) = R * R ^ (23 / 11 : ℝ) := by
    rw [show (34 / 11 : ℝ) = 1 + 23 / 11 by norm_num, Real.rpow_add hR, Real.rpow_one]
  rw [h34]
  have hA : 0 < R ^ (23 / 11 : ℝ) := Real.rpow_pos_of_pos hR _
  have hB : 0 < S ^ (23 / 22 : ℝ) := Real.rpow_pos_of_pos hS _
  have hC : 0 < e ^ (-(23 / 11) : ℝ) := Real.rpow_pos_of_pos he _
  field_simp

end UnforcedLeray.Short.PartIIIb.Concrete.RepFarBoxIdent
