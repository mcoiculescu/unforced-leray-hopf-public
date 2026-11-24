import UnforcedLeray.Short.PartI.Sub.T02_1_2_4

/-!
# Scalar kernel bound for the weighted Duhamel estimate (task `PartI:T02/1/2/4/1`)

Helper for `bilWeightedEstimate` (`Short/PartI/Tasks/LocalClassicalBounded/HkPersistence/

the November 2 reference manuscript`, lines 261-288.

* `heatDivL2Coeff_nonneg'`: the Gaussian coefficient is nonnegative.
* `heatDiv_exp_integral_le`: the exponentially weighted Gaussian Duhamel kernel integral
  `∫_{(0,t)} heatDivL2Coeff(ν(t-r)) e^{λ r} dr ≤ 2 ν^{-1/2} (λ^{1/2})^{-1} e^{λ t}`.
  It is reduced to the library square-root Volterra kernel bound
  `UnforcedLeray.Infra.VolterraEvolution.integral_kernel_mul_exp_le`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Real
open UnforcedLeray.HeatCylinder

namespace UnforcedLeray.Short.PartI.BilWE

theorem heatDivL2Coeff_nonneg' (θ : ℝ) : 0 ≤ heatDivL2Coeff θ := by
  unfold heatDivL2Coeff
  positivity

/-- The weighted Gaussian Duhamel kernel integral on `(0,t)`. -/
theorem heatDiv_exp_integral_le {ν lam t : ℝ} (hν : 0 < ν) (hlam : 0 < lam) (ht : 0 ≤ t) :
    ∫ r in Ioo 0 t, heatDivL2Coeff (ν * (t - r)) * Real.exp (lam * r) ≤
      2 * ν ^ (-(1 / 2 : ℝ)) / Real.sqrt lam * Real.exp (lam * t) := by
  have h1 : ∫ r in Ioo 0 t, heatDivL2Coeff (ν * (t - r)) * Real.exp (lam * r) =
      ∫ r in (0 : ℝ)..t, (2 / Real.sqrt Real.pi * ν ^ (-(1 / 2 : ℝ))) *
        ((t - r) ^ (-(1 / 2 : ℝ)) * Real.exp (lam * (r - 0))) := by
    rw [intervalIntegral.integral_of_le ht, integral_Ioc_eq_integral_Ioo]
    refine setIntegral_congr_fun measurableSet_Ioo ?_
    intro r hr
    dsimp only
    have hτ : 0 < t - r := sub_pos.mpr hr.2
    rw [heatDivL2Coeff_eq_singular hν hτ, sub_zero]
    ring
  have hk := UnforcedLeray.Infra.VolterraEvolution.integral_kernel_mul_exp_le
    (lam := lam) (s := 0) (τ := t) hlam ht
  rw [Real.Gamma_one_half_eq] at hk
  have hpow : (1 / lam) ^ (1 / 2 : ℝ) = 1 / Real.sqrt lam := by
    rw [Real.sqrt_eq_rpow, Real.div_rpow zero_le_one hlam.le, Real.one_rpow]
  rw [hpow] at hk
  rw [h1, intervalIntegral.integral_const_mul]
  simp only [sub_zero] at hk ⊢
  have hπ : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.2 Real.pi_pos).ne'
  have hcoef : 0 ≤ 2 / Real.sqrt Real.pi * ν ^ (-(1 / 2 : ℝ)) := by positivity
  refine (mul_le_mul_of_nonneg_left hk hcoef).trans_eq ?_
  field_simp

end UnforcedLeray.Short.PartI.BilWE
