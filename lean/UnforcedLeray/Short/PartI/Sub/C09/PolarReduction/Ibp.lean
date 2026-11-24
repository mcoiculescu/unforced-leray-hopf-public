import UnforcedLeray.Short.PartI.Sub.C09
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Helper for `polarReduction`: periodic integration by parts against the angular mode `e^{2iθ}`

For `h : ℝ → ℂ` smooth with `h(-π) = h(π)` and `h'(-π) = h'(π)`,
`∫_{-π}^{π} e^{2iθ} h''(θ) dθ = -4 ∫_{-π}^{π} e^{2iθ} h(θ) dθ`  (`ibp_ang_second`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Real
open scoped ContDiff

namespace UnforcedLeray.Short.PartI.PolarRed

theorem hasDerivAt_ang (θ : ℝ) :
    HasDerivAt (fun τ : ℝ => Complex.exp (2 * Complex.I * (τ : ℂ)))
      (Complex.exp (2 * Complex.I * (θ : ℂ)) * (2 * Complex.I)) θ := by
  have h1 : HasDerivAt (fun τ : ℝ => 2 * Complex.I * (τ : ℂ)) (2 * Complex.I) θ := by
    simpa using ((hasDerivAt_id' θ).ofReal_comp).const_mul (2 * Complex.I)
  exact h1.cexp

theorem ang_pi : Complex.exp (2 * Complex.I * ((π : ℝ) : ℂ)) = 1 := by
  rw [Complex.exp_eq_one_iff]
  exact ⟨1, by push_cast; ring⟩

theorem ang_neg_pi : Complex.exp (2 * Complex.I * ((-π : ℝ) : ℂ)) = 1 := by
  rw [Complex.exp_eq_one_iff]
  exact ⟨-1, by push_cast; ring⟩

/-- Periodic integration by parts twice against `e^{2iθ}`. -/
theorem ibp_ang_second {h : ℝ → ℂ} (hh : ContDiff ℝ ∞ h) (hper : h (-π) = h π)
    (hper' : deriv h (-π) = deriv h π) :
    ∫ θ in (-π)..π, Complex.exp (2 * Complex.I * (θ : ℂ)) * deriv (deriv h) θ =
      -4 * ∫ θ in (-π)..π, Complex.exp (2 * Complex.I * (θ : ℂ)) * h θ := by
  have hd1 : ContDiff ℝ ∞ (deriv h) := (contDiff_infty_iff_deriv.1 hh).2
  have hd2 : ContDiff ℝ ∞ (deriv (deriv h)) := (contDiff_infty_iff_deriv.1 hd1).2
  have hE : Continuous (fun τ : ℝ => Complex.exp (2 * Complex.I * (τ : ℂ))) :=
    continuous_iff_continuousAt.2 fun θ => (hasDerivAt_ang θ).continuousAt
  have hE' : Continuous (fun τ : ℝ => Complex.exp (2 * Complex.I * (τ : ℂ)) * (2 * Complex.I)) :=
    hE.mul continuous_const
  have hdiff : ∀ x : ℝ, HasDerivAt h (deriv h x) x := fun x =>
    ((hh.differentiable (by simp)) x).hasDerivAt
  have hdiff1 : ∀ x : ℝ, HasDerivAt (deriv h) (deriv (deriv h) x) x := fun x =>
    ((hd1.differentiable (by simp)) x).hasDerivAt
  have s1 := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := -π) (b := π)
    (u := fun τ : ℝ => Complex.exp (2 * Complex.I * (τ : ℂ)))
    (u' := fun τ : ℝ => Complex.exp (2 * Complex.I * (τ : ℂ)) * (2 * Complex.I))
    (v := deriv h) (v' := deriv (deriv h))
    (fun x _ => hasDerivAt_ang x) (fun x _ => hdiff1 x)
    (hE'.intervalIntegrable _ _) (hd2.continuous.intervalIntegrable _ _)
  have s2 := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := -π) (b := π)
    (u := fun τ : ℝ => Complex.exp (2 * Complex.I * (τ : ℂ)))
    (u' := fun τ : ℝ => Complex.exp (2 * Complex.I * (τ : ℂ)) * (2 * Complex.I))
    (v := h) (v' := deriv h)
    (fun x _ => hasDerivAt_ang x) (fun x _ => hdiff x)
    (hE'.intervalIntegrable _ _) (hd1.continuous.intervalIntegrable _ _)
  have s3 : ∫ x in (-π)..π, Complex.exp (2 * Complex.I * (x : ℂ)) * (2 * Complex.I) * deriv h x =
      2 * Complex.I * ∫ x in (-π)..π, Complex.exp (2 * Complex.I * (x : ℂ)) * deriv h x := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext x
    ring
  have s4 : ∫ x in (-π)..π, Complex.exp (2 * Complex.I * (x : ℂ)) * (2 * Complex.I) * h x =
      2 * Complex.I * ∫ x in (-π)..π, Complex.exp (2 * Complex.I * (x : ℂ)) * h x := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext x
    ring
  simp only [ang_pi, ang_neg_pi, hper, hper', one_mul, sub_self, zero_sub] at s1 s2
  rw [s3] at s1
  rw [s4] at s2
  rw [s2] at s1
  rw [s1]
  linear_combination (4 * ∫ θ in (-π)..π, Complex.exp (2 * Complex.I * (θ : ℂ)) * h θ) *
    Complex.I_sq

end UnforcedLeray.Short.PartI.PolarRed
