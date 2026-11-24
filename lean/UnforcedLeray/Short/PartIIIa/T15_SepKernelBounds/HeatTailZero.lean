import UnforcedLeray.Short.PartIIIa.Sub.T15

/-!
# Part III-a, task `PartIII-a:T15/7`: the Newtonian potential as a heat integral

Proves `heatTailZero : HeatTailZero` (`Sub/T15.lean`): for `x ≠ 0`,
`H_0(x) = ∫_{(0,∞)} G_a(x) da = (4π‖x‖)⁻¹`, where `G_a(x) = (4πa)^{-3/2} e^{-‖x‖²/(4a)}`
(source: `the November 2 reference manuscript`, SP 3604-3610).

1. Inversion `a = 1/u` (Mathlib `integral_comp_rpow_Ioi` with exponent `p = -1`). The integrand
   becomes `u^{-2} G_{1/u}(x) = (4π)^{-3/2} u^{-1/2} e^{-(‖x‖²/4) u}`.
2. Gamma integral (`Real.integral_rpow_mul_exp_neg_mul_Ioi`, `a = 1/2`, `r = ‖x‖²/4`): the
   integral is `(4/‖x‖²)^{1/2} Γ(1/2) = (2/‖x‖) √π`.
3. Arithmetic: `(4π)^{-3/2} = (4π)⁻¹ (2√π)⁻¹`, so the total is `(4π)⁻¹ ‖x‖⁻¹ = (4π‖x‖)⁻¹`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

/-- Pointwise form of the substitution `a = 1/u` on `(0,∞)`. -/
lemma heatTailZero_integrand (x : Space) {u : ℝ} (hu : 0 < u) :
    (|(-1 : ℝ)| * u ^ ((-1 : ℝ) - 1)) • heatG (u ^ (-1 : ℝ)) x =
      (4 * Real.pi) ^ (-3 / 2 : ℝ) * (u ^ ((1 / 2 : ℝ) - 1) * Real.exp (-((‖x‖ ^ 2 / 4) * u))) := by
  have hu0 : u ≠ 0 := hu.ne'
  have hpi : (0 : ℝ) ≤ 4 * Real.pi := by positivity
  have hinv : (u⁻¹) ^ (-3 / 2 : ℝ) = u ^ (3 / 2 : ℝ) := by
    rw [show (-3 / 2 : ℝ) = -(3 / 2) by norm_num, Real.rpow_neg (inv_nonneg.mpr hu.le),
      Real.inv_rpow hu.le, inv_inv]
  have hpow : (4 * Real.pi * u ^ (-1 : ℝ)) ^ (-3 / 2 : ℝ) =
      (4 * Real.pi) ^ (-3 / 2 : ℝ) * u ^ (3 / 2 : ℝ) := by
    rw [Real.rpow_neg_one, Real.mul_rpow hpi (inv_nonneg.mpr hu.le), hinv]
  have hexp : -‖x‖ ^ 2 / (4 * u ^ (-1 : ℝ)) = -((‖x‖ ^ 2 / 4) * u) := by
    rw [Real.rpow_neg_one]
    field_simp
  have hpow2 : u ^ ((-1 : ℝ) - 1) * u ^ (3 / 2 : ℝ) = u ^ ((1 / 2 : ℝ) - 1) := by
    rw [← Real.rpow_add hu]
    congr 1
    norm_num
  simp only [heatG, smul_eq_mul]
  rw [abs_neg, abs_one, hpow, hexp, ← hpow2]
  ring

/-- **The Newtonian potential as a heat integral** (`PartIII-a:T15/7`; SP 3604-3610):
`∫_{(0,∞)} G_a(x) da = (4π‖x‖)⁻¹` for `x ≠ 0`. -/
theorem heatTailZero : UnforcedLeray.Short.IIIa.HeatTailZero := by
  unfold UnforcedLeray.Short.IIIa.HeatTailZero
  intro x hx
  have hR : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hRne : ‖x‖ ≠ 0 := hR.ne'
  have key : ∫ t in Ioi (0 : ℝ), (|(-1 : ℝ)| * t ^ ((-1 : ℝ) - 1)) • heatG (t ^ (-1 : ℝ)) x =
      ∫ y in Ioi (0 : ℝ), heatG y x :=
    integral_comp_rpow_Ioi (fun a => heatG a x) (by norm_num)
  have hstep : heatTail 0 x = ∫ u in Ioi (0 : ℝ),
      (4 * Real.pi) ^ (-3 / 2 : ℝ) * (u ^ ((1 / 2 : ℝ) - 1) * Real.exp (-((‖x‖ ^ 2 / 4) * u))) := by
    unfold heatTail
    rw [← key]
    refine setIntegral_congr_fun measurableSet_Ioi (fun u hu => ?_)
    exact heatTailZero_integrand x (mem_Ioi.mp hu)
  have hB : (1 / (‖x‖ ^ 2 / 4)) ^ (1 / 2 : ℝ) = 2 / ‖x‖ := by
    rw [← Real.sqrt_eq_rpow, show (1 / (‖x‖ ^ 2 / 4)) = (2 / ‖x‖) ^ 2 by ring,
      Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 2 / ‖x‖)]
  have hs4 : Real.sqrt (4 * Real.pi) = 2 * Real.sqrt Real.pi := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  have hA : (4 * Real.pi) ^ (-3 / 2 : ℝ) = (4 * Real.pi)⁻¹ * (2 * Real.sqrt Real.pi)⁻¹ := by
    rw [show (-3 / 2 : ℝ) = -1 + -(1 / 2) by norm_num,
      Real.rpow_add (by positivity : (0 : ℝ) < 4 * Real.pi), Real.rpow_neg_one,
      Real.rpow_neg (by positivity : (0 : ℝ) ≤ 4 * Real.pi), ← Real.sqrt_eq_rpow, hs4]
  have hsp : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  rw [hstep, integral_const_mul,
    Real.integral_rpow_mul_exp_neg_mul_Ioi (by norm_num : (0 : ℝ) < 1 / 2)
      (div_pos (pow_pos hR 2) (by norm_num : (0 : ℝ) < 4)),
    Real.Gamma_one_half_eq, hB, hA]
  field_simp

end UnforcedLeray.Short.IIIa
