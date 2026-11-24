import UnforcedLeray.Infra.VolterraEvolution.Kernel
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# The Beta integral for the square-root Volterra kernel

* `integral_rpow_mul_one_sub_rpow`: the real Beta integral
  `∫₀¹ u^{a-1} (1-u)^{b-1} du = Γ(a) Γ(b) / Γ(a+b)` for `a, b > 0`;
* `integral_kernel_mul_rpow`: for `s ≤ τ` and `α > -1`,
  `∫ r in s..τ, (τ - r)^{-1/2} (r - s)^α dr = (τ - s)^{α + 1/2} Γ(α+1) Γ(1/2) / Γ(α + 3/2)`.

This is the Gamma recursion behind the iterated Picard bound
`(C Γ(1/2))ⁿ (τ - s)^{n/2} / Γ(n/2 + 1)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set intervalIntegral Real

namespace UnforcedLeray.Infra.VolterraEvolution

/-- The real Beta integral. -/
theorem integral_rpow_mul_one_sub_rpow {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ u in (0 : ℝ)..1, u ^ (a - 1) * (1 - u) ^ (b - 1) = Gamma a * Gamma b / Gamma (a + b) := by
  have hc := Complex.Gamma_mul_Gamma_eq_betaIntegral (s := (a : ℂ)) (t := (b : ℂ))
    (by simpa using ha) (by simpa using hb)
  have hB : Complex.betaIntegral a b = ((∫ u in (0 : ℝ)..1, u ^ (a - 1) * (1 - u) ^ (b - 1) : ℝ) : ℂ) := by
    rw [Complex.betaIntegral, ← intervalIntegral.integral_ofReal]
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [uIcc_of_le zero_le_one] at hu
    simp only [Complex.ofReal_mul]
    rw [Complex.ofReal_cpow hu.1, Complex.ofReal_cpow (by linarith [hu.2] : (0 : ℝ) ≤ 1 - u)]
    push_cast
    ring
  rw [hB, ← Complex.ofReal_add, Complex.Gamma_ofReal, Complex.Gamma_ofReal,
    Complex.Gamma_ofReal] at hc
  have hc' : Gamma a * Gamma b =
      Gamma (a + b) * ∫ u in (0 : ℝ)..1, u ^ (a - 1) * (1 - u) ^ (b - 1) := by
    exact_mod_cast hc
  have hpos : 0 < Gamma (a + b) := Gamma_pos_of_pos (by linarith)
  rw [eq_div_iff hpos.ne', hc']
  ring

/-- The Beta integral for the square-root kernel on `[s, τ]`, `s < τ`, `α > -1`. -/
theorem integral_kernel_mul_rpow_of_lt {s τ α : ℝ} (h : s < τ) (hα : -1 < α) :
    ∫ r in s..τ, (τ - r) ^ (-(1 / 2 : ℝ)) * (r - s) ^ α =
      (τ - s) ^ (α + 1 / 2) * (Gamma (α + 1) * Gamma (1 / 2) / Gamma (α + 1 + 1 / 2)) := by
  set c := τ - s with hcdef
  have hc : 0 < c := by linarith
  have hsub := intervalIntegral.integral_comp_mul_add
    (f := fun r => (τ - r) ^ (-(1 / 2 : ℝ)) * (r - s) ^ α) (a := 0) (b := 1) hc.ne' s
  simp only [mul_zero, zero_add, mul_one] at hsub
  rw [show c + s = τ by rw [hcdef]; ring] at hsub
  have hint : ∫ r in s..τ, (τ - r) ^ (-(1 / 2 : ℝ)) * (r - s) ^ α =
      c * ∫ u in (0 : ℝ)..1, (τ - (c * u + s)) ^ (-(1 / 2 : ℝ)) * (c * u + s - s) ^ α := by
    rw [hsub, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]
  rw [hint]
  have hcongr : ∫ u in (0 : ℝ)..1, (τ - (c * u + s)) ^ (-(1 / 2 : ℝ)) * (c * u + s - s) ^ α =
      ∫ u in (0 : ℝ)..1, (c ^ (-(1 / 2 : ℝ)) * c ^ α) *
        (u ^ ((α + 1) - 1) * (1 - u) ^ ((1 / 2 : ℝ) - 1)) := by
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [uIcc_of_le zero_le_one] at hu
    have e1 : τ - (c * u + s) = c * (1 - u) := by rw [hcdef]; ring
    have e2 : c * u + s - s = c * u := by ring
    rw [e1, e2, mul_rpow hc.le (by linarith [hu.2]), mul_rpow hc.le hu.1,
      show α + 1 - 1 = α by ring, show (1 / 2 : ℝ) - 1 = -(1 / 2) by norm_num]
    ring
  rw [hcongr, intervalIntegral.integral_const_mul,
    integral_rpow_mul_one_sub_rpow (by linarith) (by norm_num)]
  have hpow : c * (c ^ (-(1 / 2 : ℝ)) * c ^ α) = c ^ (α + 1 / 2) := by
    rw [show α + 1 / 2 = 1 + (-(1 / 2 : ℝ) + α) by ring, rpow_add hc, rpow_add hc, rpow_one]
  rw [← mul_assoc, hpow]

/-- The Beta integral for the square-root kernel on `[s, τ]`, `s ≤ τ`, `α > -1/2`. -/
theorem integral_kernel_mul_rpow {s τ α : ℝ} (hsτ : s ≤ τ) (hα : -(1 / 2 : ℝ) < α) :
    ∫ r in s..τ, (τ - r) ^ (-(1 / 2 : ℝ)) * (r - s) ^ α =
      (τ - s) ^ (α + 1 / 2) * (Gamma (α + 1) * Gamma (1 / 2) / Gamma (α + 1 + 1 / 2)) := by
  rcases eq_or_lt_of_le hsτ with h | h
  · subst h
    rw [intervalIntegral.integral_same, sub_self, zero_rpow (by linarith)]
    ring
  · exact integral_kernel_mul_rpow_of_lt h (by linarith)

end UnforcedLeray.Infra.VolterraEvolution
