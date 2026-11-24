import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Gamma
import Std.Tactic.BVDecide.LRAT.Internal.Formula.RupAddResult

/-!
# Radial Gaussian moments and the angular integral (INF22 G5)


target G5. Units B0850 (tex 12612–12623) and B0364 (tex 6788–6801).

Main results:
* `integral_pow_odd_gauss`: `∫_0^∞ r^{2n+1} e^{-r²/4} dr = 2·4ⁿ·n!` (B0850);
* `quadrupole_64`: `∫_0^∞ r³ (r⁴/4 - 2r²) e^{-r²/4} dr = 64`, the radial moment of
  `(H_0)_rad = (r⁴/4 - 2r²)e^{-r²/4}` (B0850);
* `integral_sin_sq_mul_exp_two`: `∫_0^{2π} sin²θ e^{2iθ} dθ = -π/2` (B0850, B0364: with it,
  `Q_∞(h e^{2iϑ}) = -(2/π)∫ η² h e^{2iϑ} = ∫_0^∞ r³ h`);
* `integrableOn_pow_mul_exp_neg_sq_div_four`: the integrands are integrable on `(0, ∞)`, so the
  integrals above are genuine (no junk value).
-/

noncomputable section

set_option autoImplicit false

namespace UnforcedLeray.Gaussian

open MeasureTheory Real Set Complex
open scoped Nat

/-- `r^k e^{-r²/4}` is integrable on `(0, ∞)`. -/
theorem integrableOn_pow_mul_exp_neg_sq_div_four (k : ℕ) :
    IntegrableOn (fun r : ℝ => r ^ k * Real.exp (-r ^ 2 / 4)) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 2) (s := (k : ℝ)) (b := 1 / 4)
    (by have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith) two_pos (by norm_num)
  refine h.congr_fun (fun r hr => ?_) measurableSet_Ioi
  have hr0 : 0 ≤ r := le_of_lt hr
  simp only
  rw [Real.rpow_natCast, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  congr 2; ring

/-- **G5 (B0850).** `∫_0^∞ r^{2n+1} e^{-r²/4} dr = 2·4ⁿ·n!`. -/
theorem integral_pow_odd_gauss (n : ℕ) :
    ∫ r in Ioi (0 : ℝ), r ^ (2 * n + 1) * Real.exp (-r ^ 2 / 4) = 2 * 4 ^ n * n ! := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := ((2 * n + 1 : ℕ) : ℝ))
    (b := 1 / 4) two_pos (by have : (0 : ℝ) ≤ ((2 * n + 1 : ℕ) : ℝ) := Nat.cast_nonneg _; linarith)
    (by norm_num)
  have hcongr : ∫ r in Ioi (0 : ℝ), r ^ (2 * n + 1) * Real.exp (-r ^ 2 / 4) =
      ∫ x in Ioi (0 : ℝ), x ^ ((2 * n + 1 : ℕ) : ℝ) * Real.exp (-(1 / 4) * x ^ (2 : ℝ)) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun r hr => ?_)
    rw [Real.rpow_natCast, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    congr 2; ring
  rw [hcongr, h]
  have hq : (((2 * n + 1 : ℕ) : ℝ) + 1) / 2 = (n : ℝ) + 1 := by push_cast; ring
  have hq' : -(((2 * n + 1 : ℕ) : ℝ) + 1) / 2 = -(((n + 1 : ℕ) : ℝ)) := by push_cast; ring
  rw [hq, hq', Real.Gamma_nat_eq_factorial, Real.rpow_neg (by norm_num), Real.rpow_natCast]
  rw [div_pow, one_pow, inv_div, div_one, pow_succ]
  ring

/-- **G5 (B0850, tex 12612–12623).** `∫_0^∞ r³ (r⁴/4 - 2r²) e^{-r²/4} dr = 64`. -/
theorem quadrupole_64 :
    ∫ r in Ioi (0 : ℝ), r ^ 3 * ((r ^ 4 / 4 - 2 * r ^ 2) * Real.exp (-r ^ 2 / 4)) = 64 := by
  have h7 := integrableOn_pow_mul_exp_neg_sq_div_four 7
  have h5 := integrableOn_pow_mul_exp_neg_sq_div_four 5
  have hcongr : ∫ r in Ioi (0 : ℝ), r ^ 3 * ((r ^ 4 / 4 - 2 * r ^ 2) * Real.exp (-r ^ 2 / 4)) =
      ∫ r in Ioi (0 : ℝ), ((1 / 4) * (r ^ (2 * 3 + 1) * Real.exp (-r ^ 2 / 4)) -
        2 * (r ^ (2 * 2 + 1) * Real.exp (-r ^ 2 / 4))) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun r _ => ?_)
    ring
  rw [hcongr, integral_sub (h7.const_mul _) (h5.const_mul _), integral_const_mul,
    integral_const_mul, integral_pow_odd_gauss 3, integral_pow_odd_gauss 2]
  norm_num [Nat.factorial]

/-- `∫_0^{2π} e^{ikθ} dθ = 0` for `k ≠ 0`. -/
theorem integral_exp_nat_mul_I (k : ℕ) (hk : k ≠ 0) :
    ∫ θ in (0 : ℝ)..2 * π, Complex.exp ((k : ℂ) * I * θ) = 0 := by
  have hc : (k : ℂ) * I ≠ 0 := mul_ne_zero (by exact_mod_cast hk) Complex.I_ne_zero
  rw [integral_exp_mul_complex hc]
  have h1 : Complex.exp ((k : ℂ) * I * ((2 * π : ℝ) : ℂ)) = 1 := by
    rw [show (k : ℂ) * I * ((2 * π : ℝ) : ℂ) = k * (2 * π * I) by push_cast; ring]
    exact Complex.exp_nat_mul_two_pi_mul_I k
  rw [h1]
  simp

/-- The pointwise identity `sin²θ e^{2iθ} = -1/4 + e^{2iθ}/2 - e^{4iθ}/4`. -/
theorem sin_sq_mul_exp_two_eq (θ : ℝ) :
    (Real.sin θ : ℂ) ^ 2 * Complex.exp (2 * θ * I) =
      -1 / 4 + 1 / 2 * Complex.exp (((2 : ℕ) : ℂ) * I * θ) -
        1 / 4 * Complex.exp (((4 : ℕ) : ℂ) * I * θ) := by
  obtain ⟨u, hu⟩ : ∃ u : ℂ, u = Complex.exp (θ * I) := ⟨_, rfl⟩
  have hu0 : u ≠ 0 := by rw [hu]; exact Complex.exp_ne_zero _
  have h1 : Complex.exp (-θ * I) = u⁻¹ := by rw [hu, ← Complex.exp_neg]; congr 1; ring
  have h2 : Complex.exp (2 * θ * I) = u ^ 2 := by
    rw [hu, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have h2' : Complex.exp (((2 : ℕ) : ℂ) * I * θ) = u ^ 2 := by
    rw [hu, ← Complex.exp_nat_mul]; congr 1; ring
  have h4 : Complex.exp (((4 : ℕ) : ℂ) * I * θ) = u ^ 4 := by
    rw [hu, ← Complex.exp_nat_mul]; congr 1; ring
  have hs : (Real.sin θ : ℂ) = (u⁻¹ - u) * I / 2 := by
    rw [Complex.ofReal_sin, eq_div_iff two_ne_zero, mul_comm (Complex.sin _) 2,
      Complex.two_sin, h1, ← hu]
  rw [hs, h2, h2', h4]
  have hinv : u⁻¹ * u = 1 := inv_mul_cancel₀ hu0
  linear_combination ((u⁻¹ ^ 2 * u ^ 2 - 2 * u⁻¹ * u ^ 3 + u ^ 4) / 4) * Complex.I_sq +
    (-(u⁻¹ * u + 1) / 4 + u ^ 2 / 2) * hinv

/-- **G5 (B0850, B0364; tex 12612–12623, 6788–6801).**
`∫_0^{2π} sin²θ e^{2iθ} dθ = -π/2`. -/
theorem integral_sin_sq_mul_exp_two :
    ∫ θ in (0 : ℝ)..2 * π, (Real.sin θ : ℂ) ^ 2 * Complex.exp (2 * θ * I) = -(π / 2) := by
  simp_rw [sin_sq_mul_exp_two_eq]
  have hc : ∀ k : ℕ, IntervalIntegrable (fun θ : ℝ => Complex.exp ((k : ℂ) * I * θ))
      MeasureTheory.volume 0 (2 * π) := fun k =>
    (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).intervalIntegrable
      _ _
  rw [intervalIntegral.integral_sub ((intervalIntegrable_const).add ((hc 2).const_mul _))
      ((hc 4).const_mul _),
    intervalIntegral.integral_add intervalIntegrable_const ((hc 2).const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_exp_nat_mul_I 2 (by norm_num), integral_exp_nat_mul_I 4 (by norm_num),
    intervalIntegral.integral_const]
  simp only [sub_zero, mul_zero, add_zero, Complex.real_smul]
  push_cast
  ring

end UnforcedLeray.Gaussian
