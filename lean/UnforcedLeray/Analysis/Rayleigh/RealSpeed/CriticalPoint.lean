import UnforcedLeray.Analysis.Rayleigh.RealSpeed.Defs

/-!
# Actual critical-point consequences of the Gaussian Rayleigh equation

At a real critical point Ω(a)=c, the undivided equation remains meaningful.
For c different from the neutral Gaussian speed, its actual vorticity-gradient
coefficient is nonzero, so every pointwise solution must vanish at that point.
No limiting-absorption or critical-layer regularity is assumed.
-/

noncomputable section
namespace UnforcedLeray.Rayleigh.RealSpeed
open Sturm GaussianPotential

/-- The actual coefficient cannot vanish at a nonneutral critical point. -/
theorem coefficient_ne_zero_at_critical {a c : ℝ}
    (hΩ : neutralOmega a = c) (hc : c ≠ gaussianCriticalSpeed) :
    gaussianRayleighCoefficient a ≠ 0 := by
  unfold gaussianRayleighCoefficient gaussianOffset
  rw [hΩ]
  exact mul_ne_zero (neg_ne_zero.mpr (Wlog_pos a).ne') (sub_ne_zero.mpr hc)

/-- The real undivided Rayleigh equation forces a zero at every nonneutral
critical point, independently of the angular frequency. -/
theorem real_value_zero_at_critical {a c n : ℝ} {F : ℝ → ℝ}
    (hΩ : neutralOmega a = c) (hc : c ≠ gaussianCriticalSpeed)
    (heq : (neutralOmega a - c) * (deriv (deriv F) a - n ^ 2 * F a) -
      gaussianRayleighCoefficient a * F a = 0) : F a = 0 := by
  rw [hΩ, sub_self, zero_mul, zero_sub, neg_eq_zero] at heq
  exact (mul_eq_zero.mp heq).resolve_left (coefficient_ne_zero_at_critical hΩ hc)

/-- The same conclusion holds for the actual complex-valued equation at a
real spectral speed. -/
theorem complex_value_zero_at_critical {a c n : ℝ} {F : ℝ → ℂ}
    (hΩ : neutralOmega a = c) (hc : c ≠ gaussianCriticalSpeed)
    (heq : ((neutralOmega a : ℂ) - (c : ℂ)) *
      (deriv (deriv F) a - (n : ℂ) ^ 2 * F a) -
      (gaussianRayleighCoefficient a : ℂ) * F a = 0) : F a = 0 := by
  rw [hΩ, sub_self, zero_mul, zero_sub, neg_eq_zero] at heq
  apply (mul_eq_zero.mp heq).resolve_left
  exact_mod_cast coefficient_ne_zero_at_critical hΩ hc

end UnforcedLeray.Rayleigh.RealSpeed
