import UnforcedLeray.Analysis.Rayleigh.EnergyEstimates
import UnforcedLeray.Analysis.Sturm.NeutralProfile

/-!
# The concrete Gaussian annular Rayleigh equation

The coefficient, angular speed, and critical speed below are the manuscript's
actual Gaussian functions. Dividing their genuine differential equation by its
nonzero upper-half-plane denominator produces the shifted form used by the
energy estimates. No integrated identity or solution existence is assumed.
-/

noncomputable section
open MeasureTheory Set
namespace UnforcedLeray.Rayleigh
open GaussianPotential Sturm

/-- The actual critical Gaussian angular speed. -/
def gaussianCriticalSpeed : ℝ := Real.exp (-2)

/-- Angular speed relative to its unique critical value. -/
def gaussianOffset (t : ℝ) : ℝ := neutralOmega t - gaussianCriticalSpeed

/-- The actual logarithmic vorticity-gradient coefficient `A=-W(Ω-a*)`. -/
def gaussianRayleighCoefficient (t : ℝ) : ℝ := -Wlog t * gaussianOffset t

/-- Exact Gaussian formula, including the removable critical point. -/
theorem gaussianRayleighCoefficient_eq (t : ℝ) :
    gaussianRayleighCoefficient t =
      4 * neutralRadius t * (neutralRadius t - 2) * neutralOmega t := by
  have hw := W_mul_neutral_difference (neutralRadius t - 2)
  have hc : Wlog t * (neutralOmega t - Real.exp (-2)) =
      -4 * neutralRadius t * (neutralRadius t - 2) * neutralOmega t := by
    simpa only [sub_add_cancel, neutralOmega, Wlog, neutralRadius] using hw
  unfold gaussianRayleighCoefficient gaussianOffset gaussianCriticalSpeed
  linear_combination -hc

/-- The actual Gaussian vorticity in logarithmic radius. -/
def gaussianVorticity (t : ℝ) : ℝ :=
  (2 - 2 * neutralRadius t) * neutralOmega t

/-- The Rayleigh coefficient is the actual logarithmic vorticity derivative. -/
theorem hasDerivAt_gaussianVorticity (t : ℝ) :
    HasDerivAt gaussianVorticity (gaussianRayleighCoefficient t) t := by
  rw [gaussianRayleighCoefficient_eq]
  convert (((hasDerivAt_neutralRadius t).const_mul 2).const_sub 2).mul
    (hasDerivAt_neutralOmega t) using 1 <;> (try rfl) <;> ring

/-- The actual spectral speed relative to the critical angular speed. -/
def shiftedSpeed (c : ℂ) : ℂ := c - (gaussianCriticalSpeed : ℂ)

theorem continuous_gaussianOffset : Continuous gaussianOffset :=
  continuous_neutralOmega.sub continuous_const

@[simp] theorem shiftedSpeed_im (c : ℂ) : (shiftedSpeed c).im = c.im := by
  simp [shiftedSpeed]

theorem gaussian_denominator_eq (t : ℝ) (c : ℂ) :
    (neutralOmega t : ℂ) - c = (gaussianOffset t : ℂ) - shiftedSpeed c := by
  simp [gaussianOffset, shiftedSpeed]

/-- A genuine Gaussian Rayleigh solution on the logarithmic annulus.
Existence of such a mode is a separate spectral theorem. -/
structure GaussianAnnularMode (c : ℂ) (F : ℝ → ℂ) (l r : ℝ) : Prop where
  ordered : l ≤ r
  upper_half_plane : 0 < c.im
  regularity : ContDiff ℝ 2 F
  left_endpoint : F l = 0
  right_endpoint : F r = 0
  equation : ∀ t ∈ Ioc l r,
    ((neutralOmega t : ℂ) - c) * (deriv (deriv F) t - 4 * F t) -
      (gaussianRayleighCoefficient t : ℂ) * F t = 0

namespace GaussianAnnularMode
variable {c : ℂ} {F : ℝ → ℂ} {l r : ℝ}
  (h : GaussianAnnularMode c F l r)
include h

/-- Divide the actual ODE by its nonzero spectral factor, with all coefficients
retained exactly. -/
theorem toShifted : ShiftedAnnularMode gaussianOffset (shiftedSpeed c) F l r := by
  refine ⟨h.ordered, continuous_gaussianOffset, ?_, h.regularity,
    h.left_endpoint, h.right_endpoint, ?_⟩
  · simpa only [shiftedSpeed_im] using h.upper_half_plane
  · intro t ht
    have hc : 0 < (shiftedSpeed c).im := by
      simpa only [shiftedSpeed_im] using h.upper_half_plane
    have hd : (neutralOmega t : ℂ) - c ≠ 0 := by
      rw [gaussian_denominator_eq]
      exact criticalDenominator_ne_zero (gaussianOffset t) hc
    have he := sub_eq_zero.mp (h.equation t ht)
    calc
      deriv (deriv F) t - 4 * F t =
          ((gaussianRayleighCoefficient t : ℂ) * F t) /
            ((neutralOmega t : ℂ) - c) := by
        apply (eq_div_iff hd).mpr
        simpa only [mul_comm] using he
      _ = -((Wlog t : ℂ) * criticalRatio (gaussianOffset t) (shiftedSpeed c)) * F t := by
        rw [gaussian_denominator_eq]
        simp only [gaussianRayleighCoefficient, Complex.ofReal_mul,
          Complex.ofReal_neg, criticalRatio, div_eq_mul_inv]
        ring

/-- The imaginary critical-layer moment for the manuscript's actual coefficients. -/
theorem imaginary_moment_zero :
    (∫ t in Ioc l r,
      Wlog t * gaussianOffset t / denominator (gaussianOffset t) (shiftedSpeed c) *
        ‖F t‖ ^ 2) = 0 :=
  h.toShifted.imaginary_moment_zero

/-- Exact positive energy representation for the actual Gaussian mode. -/
theorem energy_eq_square_coefficient :
    intervalEnergy F l r = ∫ t in Ioc l r,
      Wlog t * (gaussianOffset t ^ 2 / denominator (gaussianOffset t) (shiftedSpeed c)) *
        ‖F t‖ ^ 2 :=
  h.toShifted.energy_eq_square_coefficient

/-- Energy cancellation with no reciprocal-imaginary-speed loss. -/
theorem energy_eq_potential_sub :
    intervalEnergy F l r = (∫ t in Ioc l r, Wlog t * ‖F t‖ ^ 2) -
      Complex.normSq (shiftedSpeed c) * (∫ t in Ioc l r,
        Wlog t / denominator (gaussianOffset t) (shiftedSpeed c) * ‖F t‖ ^ 2) :=
  h.toShifted.energy_eq_potential_sub

/-- The normalized actual mode has a bound independent of its imaginary speed. -/
theorem normalized_energy_bounds (hmass : (∫ t in Ioc l r, ‖F t‖ ^ 2) = 1) :
    4 ≤ intervalEnergy F l r ∧ intervalEnergy F l r ≤ 8 :=
  h.toShifted.normalized_energy_bounds hmass

end GaussianAnnularMode
end UnforcedLeray.Rayleigh
