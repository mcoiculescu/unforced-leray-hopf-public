import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Scalar kernel estimates for the square-root Volterra kernel

The Volterra construction of an evolution family with square-root smoothing
(`paper/main.tex`, Section `sec:st18-265`, lines 292-306) controls the integral operator
`f ↦ ∫ r in s..τ, (τ - r) ^ (-1/2) f r` in an exponentially weighted sup norm.
This file contains the scalar estimate behind that control:

* `integral_rpow_neg_half_mul_exp_le`:
  `∫ σ in 0..t, σ ^ (-1/2) * exp (-(λ σ)) ≤ (1/λ) ^ (1/2) * Γ(1/2)` for `λ > 0`, `t ≥ 0`;
* `integral_kernel_mul_exp_le`: the weighted form
  `∫ r in s..τ, (τ - r) ^ (-1/2) * exp (λ (r - s)) ≤ (1/λ) ^ (1/2) Γ(1/2) exp (λ (τ - s))`.

Together with the choice of a large `λ` these give a contraction factor `< 1`, which replaces
the iterated Beta-function bound of the classical Picard argument.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set intervalIntegral Real

namespace UnforcedLeray.Infra.VolterraEvolution

/-- The square-root Volterra kernel `σ ↦ σ ^ (-1/2)` is interval integrable on every interval. -/
theorem intervalIntegrable_rpow_neg_half (a b : ℝ) :
    IntervalIntegrable (fun σ : ℝ => σ ^ (-(1 / 2 : ℝ))) volume a b :=
  intervalIntegrable_rpow' (by norm_num)

/-- The reflected kernel `r ↦ (τ - r) ^ (-1/2)` is interval integrable on every interval. -/
theorem intervalIntegrable_kernel (τ a b : ℝ) :
    IntervalIntegrable (fun r : ℝ => (τ - r) ^ (-(1 / 2 : ℝ))) volume a b := by
  have h := (intervalIntegrable_rpow_neg_half (τ - a) (τ - b)).comp_sub_left τ
  simpa only [sub_sub_cancel] using h

/-- The weighted kernel `r ↦ (τ - r) ^ (-1/2) e^{λ(r - s)}` is interval integrable. -/
theorem intervalIntegrable_kernel_mul_exp (τ s lam a b : ℝ) :
    IntervalIntegrable (fun r : ℝ => (τ - r) ^ (-(1 / 2 : ℝ)) * exp (lam * (r - s))) volume a b :=
  (intervalIntegrable_kernel τ a b).mul_continuousOn
    (continuous_exp.comp (continuous_const.mul (continuous_id.sub continuous_const))).continuousOn

/-- The Gamma integrand `σ ^ (-1/2) e^{-λσ}` is integrable on `(0, ∞)` for `λ > 0`. -/
theorem integrableOn_rpow_neg_half_mul_exp {lam : ℝ} (hlam : 0 < lam) :
    IntegrableOn (fun σ : ℝ => σ ^ (-(1 / 2 : ℝ)) * exp (-(lam * σ))) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := -(1 / 2 : ℝ)) (b := lam)
    (by norm_num) one_pos hlam
  refine h.congr_fun (fun σ _ => ?_) measurableSet_Ioi
  simp only [rpow_one, neg_mul]

/-- Truncated Gamma bound: `∫₀ᵗ σ^{-1/2} e^{-λσ} dσ ≤ (1/λ)^{1/2} Γ(1/2)`. -/
theorem integral_rpow_neg_half_mul_exp_le {lam t : ℝ} (hlam : 0 < lam) (ht : 0 ≤ t) :
    ∫ σ in (0 : ℝ)..t, σ ^ (-(1 / 2 : ℝ)) * exp (-(lam * σ))
      ≤ (1 / lam) ^ (1 / 2 : ℝ) * Gamma (1 / 2) := by
  rw [intervalIntegral.integral_of_le ht]
  have hfull := integral_rpow_mul_exp_neg_mul_Ioi (a := 1 / 2) (r := lam) (by norm_num) hlam
  have hexp : (1 / 2 : ℝ) - 1 = -(1 / 2) := by norm_num
  rw [hexp] at hfull
  rw [← hfull]
  refine setIntegral_mono_set (integrableOn_rpow_neg_half_mul_exp hlam) ?_ ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with σ hσ
    exact mul_nonneg (rpow_nonneg (le_of_lt hσ) _) (exp_pos _).le
  · exact (Ioc_subset_Ioi_self).eventuallyLE

/-- The weighted square-root kernel bound used for the Volterra contraction:
`∫ r in s..τ, (τ - r)^{-1/2} e^{λ(r-s)} dr ≤ (1/λ)^{1/2} Γ(1/2) e^{λ(τ-s)}`. -/
theorem integral_kernel_mul_exp_le {lam s τ : ℝ} (hlam : 0 < lam) (hsτ : s ≤ τ) :
    ∫ r in s..τ, (τ - r) ^ (-(1 / 2 : ℝ)) * exp (lam * (r - s))
      ≤ (1 / lam) ^ (1 / 2 : ℝ) * Gamma (1 / 2) * exp (lam * (τ - s)) := by
  have hrw : ∀ r : ℝ, (τ - r) ^ (-(1 / 2 : ℝ)) * exp (lam * (r - s))
      = exp (lam * (τ - s)) * ((τ - r) ^ (-(1 / 2 : ℝ)) * exp (-(lam * (τ - r)))) := by
    intro r
    have : lam * (r - s) = lam * (τ - s) + -(lam * (τ - r)) := by ring
    rw [this, exp_add]
    ring
  simp_rw [hrw]
  rw [intervalIntegral.integral_const_mul]
  have hsub := intervalIntegral.integral_comp_sub_left
    (fun σ : ℝ => σ ^ (-(1 / 2 : ℝ)) * exp (-(lam * σ))) (a := s) (b := τ) τ
  simp only [sub_self] at hsub
  rw [hsub, mul_comm]
  exact mul_le_mul_of_nonneg_right (integral_rpow_neg_half_mul_exp_le hlam (by linarith))
    (exp_pos _).le

/-- The unweighted kernel integral: `∫ r in s..τ, (τ - r)^{-1/2} dr = 2 (τ - s)^{1/2}`. -/
theorem integral_kernel {s τ : ℝ} :
    ∫ r in s..τ, (τ - r) ^ (-(1 / 2 : ℝ)) = 2 * (τ - s) ^ (1 / 2 : ℝ) := by
  have hsub := intervalIntegral.integral_comp_sub_left
    (fun σ : ℝ => σ ^ (-(1 / 2 : ℝ))) (a := s) (b := τ) τ
  simp only [sub_self] at hsub
  rw [hsub, integral_rpow (Or.inl (by norm_num))]
  rw [show -(1 / 2 : ℝ) + 1 = 1 / 2 by norm_num, zero_rpow (by norm_num)]
  ring

end UnforcedLeray.Infra.VolterraEvolution
