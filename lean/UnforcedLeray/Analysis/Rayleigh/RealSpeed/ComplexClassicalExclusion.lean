import UnforcedLeray.Analysis.Rayleigh.RealSpeed.ClassicalExclusion
import UnforcedLeray.Analysis.Rayleigh.RealSpeed.ComplexProjection
import UnforcedLeray.Analysis.Sturm.NeutralCriticalSpeed
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Exclusion of all real Gaussian Rayleigh speeds for complex classical H² modes

The noncritical real theorem applies to the proved real and imaginary component
equations. The critical value is handled by the independently proved neutral
kernel exclusion, where the vanishing coefficient is cancelled only away from
its zero and continuity then recovers the equation at that point.

The hypotheses are concrete C² regularity, actual value/derivative L² membership,
and the actual undivided Gaussian Rayleigh equation. Existence or regularity
of a limiting mode is not supplied by this module.
-/

noncomputable section
open MeasureTheory
namespace UnforcedLeray.Rayleigh.RealSpeed
open Sturm

/-- Every actual complex C² H² whole-line Gaussian Rayleigh mode at a real
speed is identically zero, including the critical speed c=exp(-2). -/
theorem classical_complex_real_mode_eq_zero {c : ℝ} {g : ℝ → ℂ}
    (hgc : ContDiff ℝ 2 g) (hg : MemLp g 2 volume)
    (hdg : MemLp (deriv g) 2 volume)
    (hddg : MemLp (deriv (deriv g)) 2 volume)
    (heq : ∀ t, ((neutralOmega t : ℂ) - (c : ℂ)) *
      (deriv (deriv g) t - 4 * g t) - (gaussianRayleighCoefficient t : ℂ) * g t = 0) :
    g = 0 := by
  by_cases hc : c = gaussianCriticalSpeed
  · subst c
    exact gaussian_critical_rayleigh_mode_eq_zero hgc hg hdg heq
  · have hr : (fun t => (g t).re) = 0 :=
      classical_real_mode_eq_zero_of_ne_critical hc (re_contDiff_two hgc) hg.re
        (re_deriv_memLp (hgc.differentiable (by norm_num)) hdg)
        (re_second_memLp hgc hddg) (re_undivided_equation hgc heq)
    have hi : (fun t => (g t).im) = 0 :=
      classical_real_mode_eq_zero_of_ne_critical hc (im_contDiff_two hgc) hg.im
        (im_deriv_memLp (hgc.differentiable (by norm_num)) hdg)
        (im_second_memLp hgc hddg) (im_undivided_equation hgc heq)
    funext t
    apply Complex.ext
    · exact congrFun hr t
    · exact congrFun hi t

/-- The real-valued version also covers every real speed, without excluding
the critical value from its hypotheses. -/
theorem classical_real_mode_eq_zero {c : ℝ} {f : ℝ → ℝ}
    (hfc : ContDiff ℝ 2 f) (hf : MemLp f 2 volume)
    (hdf : MemLp (deriv f) 2 volume)
    (hddf : MemLp (deriv (deriv f)) 2 volume)
    (heq : ∀ t, (neutralOmega t - c) * (deriv (deriv f) t - 4 * f t) -
      gaussianRayleighCoefficient t * f t = 0) : f = 0 := by
  have hfirst : deriv (fun t => (f t : ℂ)) = fun t => Complex.ofReal (deriv f t) := by
    funext t
    exact ((hfc.differentiable (by norm_num) t).hasDerivAt.ofReal_comp).deriv
  have hsecond : deriv (deriv (fun t => (f t : ℂ))) =
      fun t => Complex.ofReal (deriv (deriv f) t) := by
    rw [hfirst]
    funext t
    exact ((hfc.differentiable_deriv_two t).hasDerivAt.ofReal_comp).deriv
  have hz : (fun t => (f t : ℂ)) = 0 := by
    apply classical_complex_real_mode_eq_zero (c := c) (g := fun t => (f t : ℂ))
      (Complex.ofRealCLM.contDiff.comp hfc) hf.ofReal
    · rw [hfirst]
      exact hdf.ofReal
    · rw [hsecond]
      exact hddf.ofReal
    · intro t
      rw [hsecond]
      have h := congrArg (fun x : ℝ => (x : ℂ)) (heq t)
      simpa only [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_ofNat,
        Complex.ofReal_zero] using h
  funext t
  have ht := congrArg Complex.re (congrFun hz t)
  simpa using ht

end UnforcedLeray.Rayleigh.RealSpeed
