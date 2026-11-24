import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.TransTable.ThinChart.QInt

/-!
# `ThinChart/Core1`: pointwise algebra, the window, one `q`-cell (source 2697, 2706, 2717-2723)
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

namespace TC

/-- The pointwise algebra of `W²(|v|s^{-1/2}f)² = (W|v|)²·(s⁻¹f²)`. -/
theorem weight_alg {W a s : ℝ} (hW : 0 ≤ W) (hs : 0 < s) (f : ℝ≥0∞) :
    ENNReal.ofReal (W ^ 2) * (ENNReal.ofReal (a * (Real.sqrt s)⁻¹) * f) ^ (2 : ℝ) =
      (ENNReal.ofReal W * ENNReal.ofReal a) ^ (2 : ℝ) *
        (ENNReal.ofReal s⁻¹ * f ^ (2 : ℝ)) := by
  have hsq : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
  simp only [ENNReal.rpow_two]
  rw [ENNReal.ofReal_pow hW, ENNReal.ofReal_mul' (inv_nonneg.2 hsq.le)]
  have h1 : ENNReal.ofReal (Real.sqrt s)⁻¹ ^ 2 = ENNReal.ofReal s⁻¹ := by
    rw [← ENNReal.ofReal_pow (inv_nonneg.2 hsq.le), inv_pow, Real.sq_sqrt hs.le]
  rw [← h1]
  ring

/-- Outside the window `4/(5ν) ≤ s ≤ 1/ν` the chart point is not in the annulus. -/
theorem window_of_mem {R ν s η : ℝ} (hR : 0 < R) (hν : 0 < ν) (hs : 0 < s)
    (h : (!₂[R / Real.sqrt s, 0, η / Real.sqrt s] : Space) ∈ streamAnn ν R) :
    4 / (5 * ν) ≤ s ∧ s ≤ 1 / ν := by
  obtain ⟨h1, h2⟩ := h
  have hsq : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
  have hsν : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
  have hρ : ϱ (!₂[R / Real.sqrt s, 0, η / Real.sqrt s] : Space) = R / Real.sqrt s := by
    unfold ϱ
    simp only [PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    rw [show (0 : ℝ) ^ 2 = 0 by norm_num, add_zero, Real.sqrt_sq (by positivity)]
  rw [hρ] at h1 h2
  have e5 : Real.sqrt (5 * ν / 4) ^ 2 = 5 * ν / 4 := Real.sq_sqrt (by positivity)
  have e1 : Real.sqrt ν ^ 2 = ν := Real.sq_sqrt hν.le
  have e2 : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs.le
  constructor
  · -- R / √s ≤ R √(5ν/4)  ⇒  1 ≤ √s √(5ν/4)  ⇒  1 ≤ s (5ν/4)
    have h3 : 1 ≤ Real.sqrt s * Real.sqrt (5 * ν / 4) := by
      rw [div_le_iff₀ hsq] at h2
      have : R * 1 ≤ R * (Real.sqrt (5 * ν / 4) * Real.sqrt s) := by nlinarith
      nlinarith [le_of_mul_le_mul_left this hR]
    have h4 : 1 ≤ (Real.sqrt s * Real.sqrt (5 * ν / 4)) ^ 2 := by nlinarith
    rw [mul_pow, e2, e5] at h4
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  · have h3 : Real.sqrt s * Real.sqrt ν ≤ 1 := by
      rw [le_div_iff₀ hsq] at h1
      have : R * (Real.sqrt ν * Real.sqrt s) ≤ R * 1 := by nlinarith
      nlinarith [le_of_mul_le_mul_left this hR]
    have h4 : (Real.sqrt s * Real.sqrt ν) ^ 2 ≤ 1 := by nlinarith [mul_nonneg hsq.le hsν.le]
    rw [mul_pow, e2, e1] at h4
    rw [le_div_iff₀ hν]
    nlinarith

end TC

end UnforcedLeray.Short.PartIIIb.Concrete

end
