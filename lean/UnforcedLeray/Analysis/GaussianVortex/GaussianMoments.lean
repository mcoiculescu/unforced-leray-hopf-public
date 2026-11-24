import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic

/-!
# Actual one-dimensional Gaussian second moments

The second moment is computed from the integral of the actual derivative
of `x * exp(-b*x²)`. Integrability of that primitive and derivative supplies
the vanishing boundary terms on the whole line.
-/

noncomputable section
open MeasureTheory
namespace UnforcedLeray.GaussianVortex

/-- The actual quadratic moment is integrable for every positive Gaussian scale. -/
theorem integrable_gaussian_sq_moment {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : ℝ => x ^ 2 * Real.exp (-b * x ^ 2)) := by
  simpa only [Real.rpow_two] using
    integrable_rpow_mul_exp_neg_mul_sq hb (show (-1 : ℝ) < 2 by norm_num)

/-- The Gaussian moment relation, obtained by integrating a genuine derivative. -/
theorem gaussian_sq_moment_relation {b : ℝ} (hb : 0 < b) :
    (2 * b) * (∫ x : ℝ, x ^ 2 * Real.exp (-b * x ^ 2)) =
      ∫ x : ℝ, Real.exp (-b * x ^ 2) := by
  have hg := integrable_exp_neg_mul_sq hb
  have hq := integrable_gaussian_sq_moment hb
  have hd : ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => y * Real.exp (-b * y ^ 2))
        (Real.exp (-b * x ^ 2) - (2 * b) * (x ^ 2 * Real.exp (-b * x ^ 2))) x := by
    intro x
    convert (hasDerivAt_id x).mul ((((hasDerivAt_id x).pow 2).const_mul (-b)).exp)
      using 1 <;> (first | rfl | (dsimp; ring))
  have hz := integral_eq_zero_of_hasDerivAt_of_integrable hd
    (hg.sub (hq.const_mul (2 * b))) (integrable_mul_exp_neg_mul_sq hb)
  rw [integral_sub hg (hq.const_mul (2 * b)), integral_const_mul] at hz
  linarith

/-- Exact Gaussian second moment on the whole real line. -/
theorem integral_gaussian_sq_moment {b : ℝ} (hb : 0 < b) :
    (∫ x : ℝ, x ^ 2 * Real.exp (-b * x ^ 2)) =
      (2 * b)⁻¹ * Real.sqrt (Real.pi / b) := by
  have h := gaussian_sq_moment_relation hb
  rw [integral_gaussian] at h
  have hne : 2 * b ≠ 0 := mul_ne_zero (by norm_num) hb.ne'
  calc
    _ = Real.sqrt (Real.pi / b) / (2 * b) :=
      (eq_div_iff hne).mpr (by simpa only [mul_comm] using h)
    _ = _ := by rw [div_eq_mul_inv, mul_comm]

end UnforcedLeray.GaussianVortex
