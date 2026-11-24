import UnforcedLeray.Analysis.Rayleigh.RealSpeed.Defs
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Real components of the actual real-speed Rayleigh equation

Real and imaginary parts commute with the actual first and second classical
derivatives and preserve the stated L² memberships. At a real speed, projecting
the genuine complex undivided equation therefore gives two genuine real
undivided equations. No component equation or projection identity is assumed.
-/

noncomputable section
open MeasureTheory
namespace UnforcedLeray.Rayleigh.RealSpeed
open Sturm

/-- Real projection commutes with the actual first derivative. -/
theorem deriv_re {g : ℝ → ℂ} (hg : Differentiable ℝ g) (t : ℝ) :
    deriv (fun x => (g x).re) t = (deriv g t).re := by
  exact (Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (hg t).hasDerivAt).deriv

/-- Imaginary projection commutes with the actual first derivative. -/
theorem deriv_im {g : ℝ → ℂ} (hg : Differentiable ℝ g) (t : ℝ) :
    deriv (fun x => (g x).im) t = (deriv g t).im := by
  exact (Complex.imCLM.hasFDerivAt.comp_hasDerivAt t (hg t).hasDerivAt).deriv

/-- Real projection commutes with the actual second derivative of a C² function. -/
theorem deriv_deriv_re {g : ℝ → ℂ} (hg : ContDiff ℝ 2 g) (t : ℝ) :
    deriv (deriv (fun x => (g x).re)) t = (deriv (deriv g) t).re := by
  have hfirst : deriv (fun x => (g x).re) = fun x => (deriv g x).re :=
    funext (deriv_re (hg.differentiable (by norm_num)))
  rw [hfirst]
  exact deriv_re hg.differentiable_deriv_two t

/-- Imaginary projection commutes with the actual second derivative. -/
theorem deriv_deriv_im {g : ℝ → ℂ} (hg : ContDiff ℝ 2 g) (t : ℝ) :
    deriv (deriv (fun x => (g x).im)) t = (deriv (deriv g) t).im := by
  have hfirst : deriv (fun x => (g x).im) = fun x => (deriv g x).im :=
    funext (deriv_im (hg.differentiable (by norm_num)))
  rw [hfirst]
  exact deriv_im hg.differentiable_deriv_two t

theorem re_contDiff_two {g : ℝ → ℂ} (hg : ContDiff ℝ 2 g) :
    ContDiff ℝ 2 (fun t => (g t).re) := Complex.reCLM.contDiff.comp hg

theorem im_contDiff_two {g : ℝ → ℂ} (hg : ContDiff ℝ 2 g) :
    ContDiff ℝ 2 (fun t => (g t).im) := Complex.imCLM.contDiff.comp hg

theorem re_memLp {g : ℝ → ℂ} (hg : MemLp g 2 volume) :
    MemLp (fun t => (g t).re) 2 volume := hg.re

theorem im_memLp {g : ℝ → ℂ} (hg : MemLp g 2 volume) :
    MemLp (fun t => (g t).im) 2 volume := hg.im

theorem re_deriv_memLp {g : ℝ → ℂ} (hg : Differentiable ℝ g)
    (hd : MemLp (deriv g) 2 volume) :
    MemLp (deriv (fun t => (g t).re)) 2 volume := by
  have he : deriv (fun t => (g t).re) = fun t => (deriv g t).re := funext (deriv_re hg)
  rw [he]
  exact hd.re

theorem im_deriv_memLp {g : ℝ → ℂ} (hg : Differentiable ℝ g)
    (hd : MemLp (deriv g) 2 volume) :
    MemLp (deriv (fun t => (g t).im)) 2 volume := by
  have he : deriv (fun t => (g t).im) = fun t => (deriv g t).im := funext (deriv_im hg)
  rw [he]
  exact hd.im

theorem re_second_memLp {g : ℝ → ℂ} (hg : ContDiff ℝ 2 g)
    (hd : MemLp (deriv (deriv g)) 2 volume) :
    MemLp (deriv (deriv (fun t => (g t).re))) 2 volume := by
  have he : deriv (deriv (fun t => (g t).re)) = fun t => (deriv (deriv g) t).re :=
    funext (deriv_deriv_re hg)
  rw [he]
  exact hd.re

theorem im_second_memLp {g : ℝ → ℂ} (hg : ContDiff ℝ 2 g)
    (hd : MemLp (deriv (deriv g)) 2 volume) :
    MemLp (deriv (deriv (fun t => (g t).im))) 2 volume := by
  have he : deriv (deriv (fun t => (g t).im)) = fun t => (deriv (deriv g) t).im :=
    funext (deriv_deriv_im hg)
  rw [he]
  exact hd.im

/-- The real part satisfies the genuine real-speed undivided equation. -/
theorem re_undivided_equation {g : ℝ → ℂ} {c : ℝ} (hg : ContDiff ℝ 2 g)
    (heq : ∀ t, ((neutralOmega t : ℂ) - (c : ℂ)) *
      (deriv (deriv g) t - 4 * g t) - (gaussianRayleighCoefficient t : ℂ) * g t = 0) :
    ∀ t, (neutralOmega t - c) *
      (deriv (deriv (fun x => (g x).re)) t - 4 * (g t).re) -
      gaussianRayleighCoefficient t * (g t).re = 0 := by
  intro t
  rw [deriv_deriv_re hg t]
  have h := congrArg Complex.re (heq t)
  simpa [Complex.mul_re] using h

/-- The imaginary part satisfies the genuine real-speed undivided equation. -/
theorem im_undivided_equation {g : ℝ → ℂ} {c : ℝ} (hg : ContDiff ℝ 2 g)
    (heq : ∀ t, ((neutralOmega t : ℂ) - (c : ℂ)) *
      (deriv (deriv g) t - 4 * g t) - (gaussianRayleighCoefficient t : ℂ) * g t = 0) :
    ∀ t, (neutralOmega t - c) *
      (deriv (deriv (fun x => (g x).im)) t - 4 * (g t).im) -
      gaussianRayleighCoefficient t * (g t).im = 0 := by
  intro t
  rw [deriv_deriv_im hg t]
  have h := congrArg Complex.im (heq t)
  simpa [Complex.mul_im] using h

end UnforcedLeray.Rayleigh.RealSpeed
