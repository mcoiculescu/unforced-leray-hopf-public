import UnforcedLeray.Short.PartIIb.Sub.T22_1_1_4

/-!
# `PartII-b:T22/1/1/4/2`: Gaussian decay dominates the polynomial `(1 + |q|)^{-2}`

Leaf V2 `GaussLeRpow` of `TcVcDeriv`. For `β > 0`, `exp(-β q²) ≤ (2 + 2/β) (1 + |q|)^{-2}`.
Route: `(1 + |q|)² ≤ 2 + 2q²`, and `x e^{-x} ≤ 1` for `x ≥ 0` (from `x + 1 ≤ e^x`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb.CylPDE

theorem gaussLeRpow : UnforcedLeray.Short.IIb.CylPDE.GaussLeRpow := by
  intro β hβ
  refine ⟨2 + 2 / β, fun q => ?_⟩
  have hpos : 0 < 1 + |q| := by positivity
  have hrw : (1 + |q|) ^ (-(2 : ℝ)) = ((1 + |q|) ^ 2)⁻¹ := by
    rw [Real.rpow_neg hpos.le, Real.rpow_two]
  rw [hrw, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  have hx : 0 ≤ β * q ^ 2 := by positivity
  have hE0 : 0 ≤ Real.exp (-(β * q ^ 2)) := (Real.exp_pos _).le
  have hE1 : Real.exp (-(β * q ^ 2)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hmul : Real.exp (β * q ^ 2) * Real.exp (-(β * q ^ 2)) = 1 := by
    rw [← Real.exp_add]; simp
  have hxE : β * q ^ 2 * Real.exp (-(β * q ^ 2)) ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right
      (show β * q ^ 2 ≤ Real.exp (β * q ^ 2) by linarith [Real.add_one_le_exp (β * q ^ 2)]) hE0
    linarith
  have h1 : (1 + |q|) ^ 2 ≤ 2 + 2 * q ^ 2 := by
    nlinarith [sq_abs q, sq_nonneg (|q| - 1)]
  have h2 : Real.exp (-(β * q ^ 2)) * (1 + |q|) ^ 2 ≤
      Real.exp (-(β * q ^ 2)) * (2 + 2 * q ^ 2) :=
    mul_le_mul_of_nonneg_left h1 hE0
  have h3 : (2 / β) * (β * q ^ 2 * Real.exp (-(β * q ^ 2))) =
      2 * q ^ 2 * Real.exp (-(β * q ^ 2)) := by
    field_simp
  have h4 : (2 / β) * (β * q ^ 2 * Real.exp (-(β * q ^ 2))) ≤ (2 / β) * 1 :=
    mul_le_mul_of_nonneg_left hxE (by positivity)
  have h5 : Real.exp (-(β * q ^ 2)) * (2 + 2 * q ^ 2) =
      2 * Real.exp (-(β * q ^ 2)) + 2 * q ^ 2 * Real.exp (-(β * q ^ 2)) := by
    ring
  nlinarith [h2, h3, h4, h5, hE1]
