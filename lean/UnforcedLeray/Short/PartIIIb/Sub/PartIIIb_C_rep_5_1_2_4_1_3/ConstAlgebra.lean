import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_1_2_4_1_3.Kernel

/-!
# `PartIII-b:C/rep/5/1/2/4/1/3/3/20`: the constants of the bin majorant

Source `the November 2 reference manuscript` 5590-5591 (`ε^{3/2} s_j^{5/4}`,
`R = ε⁻¹`).  Proves `ConstAlgebra`: with `P = 2c/R` one has `2πcR = P·πR²`, the first factor is
`(√P √π R)⁻¹`, `√gapA = √(4π/5) · ((1-θ)⁻¹)^{5/2} · (R^{5/2})⁻¹ · s₀^{5/4}`, and
`(√P √π R)⁻¹ (√P + 1/√P) P πR² = √π R (1+P)`.  Hence the left side is
`√π R (1+P) F` with `F = √(4π/5) ((1-θ)⁻¹)^{5/2} (R^{5/2})⁻¹ s₀^{5/4}`, while the right side is
`2√(4π/5) √π ((1-θ)⁻¹)^{5/2} (1+P/2) R (R^{5/2})⁻¹ s₀^{5/4} = √π R (2+P) F`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete.WYCore

/-- `√(u⁵) = u^{5/2}` for `u ≥ 0`. -/
theorem constAlg_sqrt_pow5 (u : ℝ) (hu : 0 ≤ u) : Real.sqrt (u ^ 5) = u ^ (5 / 2 : ℝ) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hu]
  norm_num

/-- `(√s)^{5/2} = s^{5/4}` for `s ≥ 0`. -/
theorem constAlg_sqrt_rpow5 (s : ℝ) (hs : 0 ≤ s) :
    (Real.sqrt s) ^ (5 / 2 : ℝ) = s ^ (5 / 4 : ℝ) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hs]
  norm_num

/-- Field identity behind the constant. -/
theorem constAlg_field (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    (x * y * z)⁻¹ * (x + 1 / x) * (x ^ 2 * (y ^ 2 * z ^ 2)) = y * z * (1 + x ^ 2) := by
  have hx' : x ≠ 0 := hx.ne'
  have hy' : y ≠ 0 := hy.ne'
  have hz' : z ≠ 0 := hz.ne'
  field_simp
  ring

theorem constAlgebra : ConstAlgebra := by
  intro θ R c s0 hθ0 hθ1 hR hc hs0
  have h1θ : 0 < 1 - θ := by linarith
  have hP2 : 0 < 2 * c / R := by positivity
  have hA : 0 ≤ (2 * Real.pi * c * R)⁻¹ := by positivity
  have hu0 : 0 ≤ ((1 - θ) * R / Real.sqrt s0)⁻¹ := by
    apply inv_nonneg.mpr
    exact div_nonneg (mul_nonneg h1θ.le hR.le) (Real.sqrt_nonneg _)
  have hG0 : 0 ≤ gapA θ R s0 := by
    unfold gapA
    exact mul_nonneg (by positivity) (pow_nonneg hu0 5)
  have h1 : 0 ≤ ((2 * Real.pi * c * R)⁻¹) ^ (1 / 2 : ℝ) := Real.rpow_nonneg hA _
  have h2 : 0 ≤ Real.sqrt (gapA θ R s0) := Real.sqrt_nonneg _
  have h3 : 0 ≤ Real.sqrt (2 * c / R) + 1 / Real.sqrt (2 * c / R) := by positivity
  have h4 : 0 ≤ 2 * c / R * (Real.pi * R ^ 2) := by positivity
  rw [ENNReal.ofReal_rpow_of_nonneg hA (by norm_num), ← ENNReal.ofReal_mul h1,
    ← ENNReal.ofReal_mul (mul_nonneg h1 h2),
    ← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg h1 h2) h3)]
  apply ENNReal.ofReal_le_ofReal
  -- the real inequality
  obtain ⟨P, hPdef⟩ : ∃ P : ℝ, P = 2 * c / R := ⟨_, rfl⟩
  have hP : 0 < P := by rw [hPdef]; positivity
  have hD : 2 * Real.pi * c * R = P * (Real.pi * R ^ 2) := by
    rw [hPdef]
    field_simp
  have hcR : c / R = P / 2 := by
    rw [hPdef]
    ring
  have hRpow : R ^ (-(3 / 2 : ℝ)) = R * (R ^ (5 / 2 : ℝ))⁻¹ := by
    rw [show (-(3 / 2 : ℝ)) = 1 + -(5 / 2 : ℝ) by norm_num, Real.rpow_add hR, Real.rpow_one,
      Real.rpow_neg hR.le]
  have hA' : ((P * (Real.pi * R ^ 2))⁻¹) ^ (1 / 2 : ℝ) =
      (Real.sqrt P * Real.sqrt Real.pi * R)⁻¹ := by
    rw [← Real.sqrt_eq_rpow, Real.sqrt_inv, Real.sqrt_mul hP.le,
      Real.sqrt_mul Real.pi_pos.le, Real.sqrt_sq hR.le]
    ring
  have hm0 : 0 ≤ (1 - θ)⁻¹ := inv_nonneg.mpr h1θ.le
  have hRi0 : 0 ≤ R⁻¹ := inv_nonneg.mpr hR.le
  have hsq0 : 0 ≤ Real.sqrt s0 := Real.sqrt_nonneg _
  have hne1 : (1 - θ) ≠ 0 := h1θ.ne'
  have hneR : R ≠ 0 := hR.ne'
  have hnes : Real.sqrt s0 ≠ 0 := (Real.sqrt_pos.mpr hs0).ne'
  have hu : ((1 - θ) * R / Real.sqrt s0)⁻¹ = (1 - θ)⁻¹ * R⁻¹ * Real.sqrt s0 := by
    field_simp
  have hsqrtG : Real.sqrt (gapA θ R s0) = Real.sqrt (4 * Real.pi / 5) *
      ((1 - θ)⁻¹) ^ (5 / 2 : ℝ) * (R ^ (5 / 2 : ℝ))⁻¹ * s0 ^ (5 / 4 : ℝ) := by
    unfold gapA
    rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 4 * Real.pi / 5),
      constAlg_sqrt_pow5 _ hu0, hu,
      Real.mul_rpow (mul_nonneg hm0 hRi0) hsq0, Real.mul_rpow hm0 hRi0,
      Real.inv_rpow hR.le, constAlg_sqrt_rpow5 s0 hs0.le]
    ring
  have hpart := constAlg_field (Real.sqrt P) (Real.sqrt Real.pi) R
    (Real.sqrt_pos.mpr hP) (Real.sqrt_pos.mpr Real.pi_pos) hR
  rw [Real.sq_sqrt hP.le, Real.sq_sqrt Real.pi_pos.le] at hpart
  have e : ∀ F : ℝ, (Real.sqrt P * Real.sqrt Real.pi * R)⁻¹ * F *
      (Real.sqrt P + 1 / Real.sqrt P) * (P * (Real.pi * R ^ 2)) =
      Real.sqrt Real.pi * R * (1 + P) * F := by
    intro F
    rw [← hpart]
    ring
  have hF0 : 0 ≤ Real.sqrt (4 * Real.pi / 5) * ((1 - θ)⁻¹) ^ (5 / 2 : ℝ) *
      (R ^ (5 / 2 : ℝ))⁻¹ * s0 ^ (5 / 4 : ℝ) :=
    mul_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hm0 _))
      (inv_nonneg.mpr (Real.rpow_nonneg hR.le _))) (Real.rpow_nonneg hs0.le _)
  have hG0' : 0 ≤ Real.sqrt Real.pi * R := mul_nonneg (Real.sqrt_nonneg _) hR.le
  rw [hD, hcR, ← hPdef, hA', hsqrtG, e, wyC0, hRpow]
  nlinarith [mul_nonneg hG0' hF0]

end UnforcedLeray.Short.PartIIIb.Concrete.WYCore
