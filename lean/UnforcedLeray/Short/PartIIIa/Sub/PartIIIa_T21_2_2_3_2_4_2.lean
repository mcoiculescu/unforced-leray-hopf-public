import UnforcedLeray.Short.PartIIIa.T08_ScalingJaInvDual

/-!
# `PartIII-a:T21/2/2/3/2/4/2`: change of variables on the cell

For `R > 0`, the cell `C_{c/R}` is the image of `C_c` under `y ↦ R⁻¹ • x`, and the Jacobian of
`x ↦ R⁻¹ x` on `ℝ²` is `R⁻²`. This is the instance `d = c`, `R = R⁻¹` of
`T08.integral_cell_scale` (`∫_{cell(dR)} F = R² ∫_{cell d} F(R·)`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa.AdjE1

/-- Change of variables `x = R y` on the cell: `∫_{C_{c/R}} F = R⁻² ∫_{C_c} F(R⁻¹ x) dx`. -/
theorem cell_integral_rescale (c R : ℝ) (hR : 0 < R) (F : ℝ × ℝ → ℂ) :
    ∫ y in B0579.cell (c / R), F y = ((R ^ 2)⁻¹ : ℝ) * ∫ x in B0579.cell c, F (R⁻¹ • x) := by
  have h := UnforcedLeray.Short.IIIa.T08.integral_cell_scale (d := c) (R := R⁻¹) (inv_pos.2 hR) F
  rw [← div_eq_mul_inv] at h
  rw [h, inv_pow]

end UnforcedLeray.Short.IIIa.AdjE1
