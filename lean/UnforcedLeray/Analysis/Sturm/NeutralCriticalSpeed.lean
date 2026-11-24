import UnforcedLeray.Analysis.Sturm.NeutralKernelComplex
import UnforcedLeray.Analysis.Sturm.NeutralPotentialRegularity
import UnforcedLeray.Analysis.Rayleigh.GaussianMode

/-!
# Exclusion of the actual critical Rayleigh speed

At the critical angular speed, the Rayleigh equation has a coefficient
vanishing at one point. We cancel it only off that point, then use continuity
of the actual differential residual to recover the neutral equation everywhere.
The checked complex neutral-kernel theorem then rules out a nonzero H¹ mode.
-/

noncomputable section
open MeasureTheory
open scoped ContDiff
namespace UnforcedLeray.Sturm
open GaussianPotential Rayleigh

/-- The coefficient vanishes at exactly the explicit critical log-radius. -/
theorem gaussianOffset_ne_zero_of_ne_critical {t : ℝ}
    (ht : t ≠ neutralCriticalTime) : gaussianOffset t ≠ 0 := by
  intro hz
  have hp : neutralProfile t = 0 := by
    change Real.exp t * gaussianOffset t = 0
    rw [hz, mul_zero]
  exact ht ((neutralProfile_eq_zero_iff t).mp hp)

/-- The undivided Gaussian Rayleigh equation at c=a* implies the actual neutral
ODE at every point; the singular coefficient is never cancelled at its zero. -/
theorem neutral_equation_of_critical_rayleigh {g : ℝ → ℂ}
    (hgc : ContDiff ℝ 2 g)
    (heq : ∀ t, ((neutralOmega t : ℂ) - (gaussianCriticalSpeed : ℂ)) *
      (deriv (deriv g) t - 4 * g t) - (gaussianRayleighCoefficient t : ℂ) * g t = 0) :
    ∀ t, -deriv (deriv g) t + (4 - Wlog t) • g t = 0 := by
  let R : ℝ → ℂ := fun t => -deriv (deriv g) t + (4 - Wlog t) • g t
  have hc2 : Continuous (deriv (deriv g)) :=
    (show ContDiff ℝ 1 (deriv g) from hgc.deriv').continuous_deriv_one
  have hRc : Continuous R := hc2.neg.add
    ((continuous_const.sub continuous_Wlog).smul hgc.continuous)
  have hRae : R =ᵐ[volume] 0 := by
    filter_upwards [(volume : Measure ℝ).ae_ne neutralCriticalTime] with t ht
    have hb : (gaussianOffset t : ℂ) ≠ 0 := by
      exact_mod_cast gaussianOffset_ne_zero_of_ne_critical ht
    have hprod : (gaussianOffset t : ℂ) * R t = 0 := by
      have h := heq t
      dsimp [R]
      simp only [gaussianRayleighCoefficient, gaussianOffset,
        Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_sub,
        Complex.real_smul, Complex.ofReal_ofNat] at h ⊢
      linear_combination -h
    exact (mul_eq_zero.mp hprod).resolve_left hb
  have hR : R = 0 := MeasureTheory.Measure.eq_of_ae_eq hRae hRc continuous_zero
  intro t
  exact congrFun hR t

/-- There is no nonzero C² H¹ whole-line Gaussian Rayleigh mode at c=e⁻². -/
theorem gaussian_critical_rayleigh_mode_eq_zero {g : ℝ → ℂ}
    (hgc : ContDiff ℝ 2 g) (hg : MemLp g 2 volume)
    (hdg : MemLp (deriv g) 2 volume)
    (heq : ∀ t, ((neutralOmega t : ℂ) - (gaussianCriticalSpeed : ℂ)) *
      (deriv (deriv g) t - 4 * g t) - (gaussianRayleighCoefficient t : ℂ) * g t = 0) :
    g = 0 :=
  gaussian_complex_neutral_mode_two_eq_zero hgc hg hdg
    (neutral_equation_of_critical_rayleigh hgc heq)

end UnforcedLeray.Sturm
