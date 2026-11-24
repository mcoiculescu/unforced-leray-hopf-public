import UnforcedLeray.Analysis.Sturm.NeutralKernel
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity

/-!
# Complex neutral-mode exclusion

The real potential preserves real and imaginary parts. Their classical
first and second derivatives and L² membership are verified explicitly,
so the real neutral-kernel theorem applies to both components.
-/

noncomputable section
open MeasureTheory
open scoped ContDiff
namespace UnforcedLeray.Sturm
open GaussianPotential

private theorem deriv_complex_projection {g : ℝ → ℂ}
    (hg : Differentiable ℝ g) (L : ℂ →L[ℝ] ℝ) :
    deriv (fun t => L (g t)) = fun t => L (deriv g t) := by
  funext t
  exact (L.hasFDerivAt.comp_hasDerivAt t (hg t).hasDerivAt).deriv

private theorem second_deriv_complex_projection {g : ℝ → ℂ}
    (hg : ContDiff ℝ 2 g) (L : ℂ →L[ℝ] ℝ) :
    deriv (deriv (fun t => L (g t))) = fun t => L (deriv (deriv g) t) := by
  rw [deriv_complex_projection (hg.differentiable (by norm_num)) L]
  exact deriv_complex_projection hg.differentiable_deriv_two L

/-- Complex classical H¹ solutions of the concrete mode-two neutral equation
are zero. No real-valuedness assumption is imposed on the candidate. -/
theorem gaussian_complex_neutral_mode_two_eq_zero {g : ℝ → ℂ}
    (hgc : ContDiff ℝ 2 g) (hg : MemLp g 2 volume)
    (hdg : MemLp (deriv g) 2 volume)
    (heq : ∀ t, -deriv (deriv g) t + (4 - Wlog t) • g t = 0) : g = 0 := by
  have hdr : deriv (fun t => (g t).re) = fun t => (deriv g t).re :=
    deriv_complex_projection (hgc.differentiable (by norm_num)) Complex.reCLM
  have hdi : deriv (fun t => (g t).im) = fun t => (deriv g t).im :=
    deriv_complex_projection (hgc.differentiable (by norm_num)) Complex.imCLM
  have hddr : deriv (deriv (fun t => (g t).re)) =
      fun t => (deriv (deriv g) t).re := second_deriv_complex_projection hgc Complex.reCLM
  have hddi : deriv (deriv (fun t => (g t).im)) =
      fun t => (deriv (deriv g) t).im := second_deriv_complex_projection hgc Complex.imCLM
  have hr : (fun t => (g t).re) = 0 := by
    apply gaussian_neutral_mode_two_eq_zero
    · exact Complex.reCLM.contDiff.comp hgc
    · exact hg.re
    · rw [hdr]
      exact hdg.re
    · intro t
      rw [hddr]
      have h := congrArg Complex.re (heq t)
      simpa only [Complex.add_re, Complex.neg_re, Complex.smul_re, smul_eq_mul,
        Complex.zero_re] using h
  have hi : (fun t => (g t).im) = 0 := by
    apply gaussian_neutral_mode_two_eq_zero
    · exact Complex.imCLM.contDiff.comp hgc
    · exact hg.im
    · rw [hdi]
      exact hdg.im
    · intro t
      rw [hddi]
      have h := congrArg Complex.im (heq t)
      simpa only [Complex.add_im, Complex.neg_im, Complex.smul_im, smul_eq_mul,
        Complex.zero_im] using h
  funext t
  apply Complex.ext
  · exact congrFun hr t
  · exact congrFun hi t

end UnforcedLeray.Sturm
