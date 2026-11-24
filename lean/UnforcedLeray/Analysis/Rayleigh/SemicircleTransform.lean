import UnforcedLeray.Analysis.Rayleigh.GaussianMode
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# The rotating Gaussian Rayleigh transformation

The nonsingular upper-half-plane factor `exp(t) (Ω(t)-c)` converts the actual
mode-two Gaussian Rayleigh equation into a weighted divergence equation.
All derivatives below are computed from the Gaussian coefficients and the
original mode equation; the transformed equation is not an extra hypothesis.
-/

noncomputable section
open Set
open scoped ContDiff
namespace UnforcedLeray.Rayleigh
open Sturm

/-- Nonsingular rotating factor for an upper-half-plane spectral speed. -/
def semicircleProfile (c : ℂ) (t : ℝ) : ℂ :=
  (Real.exp t : ℂ) * ((neutralOmega t : ℂ) - c)

/-- The unknown after division by the rotating Gaussian factor. -/
def semicircleQuotient (c : ℂ) (F : ℝ → ℂ) (t : ℝ) : ℂ :=
  F t / semicircleProfile c t

theorem semicircleProfile_smooth (c : ℂ) : ContDiff ℝ ∞ (semicircleProfile c) := by
  have hΩ : ContDiff ℝ ∞ neutralOmega := by
    unfold neutralOmega neutralRadius
    fun_prop
  simpa only [semicircleProfile, Function.comp_def, Complex.ofRealCLM_apply] using!
    (Complex.ofRealCLM.contDiff.comp Real.contDiff_exp).mul
      ((Complex.ofRealCLM.contDiff.comp hΩ).sub contDiff_const)

theorem semicircleProfile_ne_zero {c : ℂ} (hc : 0 < c.im) (t : ℝ) :
    semicircleProfile c t ≠ 0 := by
  apply mul_ne_zero
  · exact Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero t)
  · exact criticalDenominator_ne_zero (neutralOmega t) hc

theorem hasDerivAt_semicircleProfile (c : ℂ) (t : ℝ) :
    HasDerivAt (semicircleProfile c)
      ((Real.exp t : ℂ) * ((1 - 2 * (neutralRadius t : ℂ)) *
        (neutralOmega t : ℂ) - c)) t := by
  convert! (Real.hasDerivAt_exp t).ofReal_comp.fun_mul
    ((hasDerivAt_neutralOmega t).ofReal_comp.sub_const c) using 1
  push_cast
  ring

theorem deriv_semicircleProfile (c : ℂ) (t : ℝ) :
    deriv (semicircleProfile c) t =
      (Real.exp t : ℂ) * ((1 - 2 * (neutralRadius t : ℂ)) *
        (neutralOmega t : ℂ) - c) :=
  (hasDerivAt_semicircleProfile c t).deriv

theorem hasDerivAt_deriv_semicircleProfile (c : ℂ) (t : ℝ) :
    HasDerivAt (deriv (semicircleProfile c))
      ((Real.exp t : ℂ) * ((1 - 8 * (neutralRadius t : ℂ) +
        4 * (neutralRadius t : ℂ)^2) * (neutralOmega t : ℂ) - c)) t := by
  have hx := (hasDerivAt_neutralRadius t).ofReal_comp
  have ho := (hasDerivAt_neutralOmega t).ofReal_comp
  have hpoly : HasDerivAt (fun s : ℝ => 1 - 2 * (neutralRadius s : ℂ))
      (-4 * (neutralRadius t : ℂ)) t := by
    convert! (hx.const_mul 2).const_sub 1 using 1
    push_cast
    ring
  have h := (Real.hasDerivAt_exp t).ofReal_comp.fun_mul ((hpoly.fun_mul ho).sub_const c)
  rw [show deriv (semicircleProfile c) = fun s =>
    (Real.exp s : ℂ) * ((1 - 2 * (neutralRadius s : ℂ)) *
      (neutralOmega s : ℂ) - c) from funext (deriv_semicircleProfile c)]
  convert! h using 1
  push_cast
  ring

/-- The extra `exp(t)` factor changes the Gaussian mode-one profile into the
inhomogeneous equation needed for the mode-two divergence transformation. -/
theorem semicircleProfile_second (c : ℂ) (t : ℝ) :
    deriv (deriv (semicircleProfile c)) t =
      semicircleProfile c t +
        (Real.exp t : ℂ) * (gaussianRayleighCoefficient t : ℂ) := by
  rw [(hasDerivAt_deriv_semicircleProfile c t).deriv,
    gaussianRayleighCoefficient_eq]
  unfold semicircleProfile
  push_cast
  ring

theorem semicircleProfile_sq_eq_exp (c : ℂ) (t : ℝ) :
    semicircleProfile c t ^ 2 =
      (Real.exp (2 * t) : ℂ) * ((neutralOmega t : ℂ) - c)^2 := by
  rw [show 2 * t = t + t by ring, Real.exp_add]
  simp only [semicircleProfile, Complex.ofReal_mul]
  ring

theorem semicircleQuotient_contDiff {c : ℂ} {F : ℝ → ℂ}
    (hF : ContDiff ℝ 2 F) (hc : 0 < c.im) :
    ContDiff ℝ 2 (semicircleQuotient c F) := by
  have hH : ContDiff ℝ 2 (semicircleProfile c) :=
    (semicircleProfile_smooth c).of_le (by simp)
  simpa only [semicircleQuotient, div_eq_mul_inv, Pi.inv_apply] using!
    hF.mul (hH.inv (semicircleProfile_ne_zero hc))

theorem semicircleProfile_mul_quotient {c : ℂ} (hc : 0 < c.im)
    (F : ℝ → ℂ) (t : ℝ) :
    semicircleProfile c t * semicircleQuotient c F t = F t := by
  unfold semicircleQuotient
  field_simp [semicircleProfile_ne_zero hc t]

/-- The flux of a quotient is its Wronskian. This identity only uses actual
first derivatives and a nonzero divisor. -/
theorem quotient_flux_eq_wronskian {H F : ℝ → ℂ}
    (hH : Differentiable ℝ H) (hF : Differentiable ℝ F)
    (hne : ∀ t, H t ≠ 0) (t : ℝ) :
    H t ^ 2 * deriv (fun s => F s / H s) t =
      H t * deriv F t - deriv H t * F t := by
  rw [((hF t).hasDerivAt.fun_div (hH t).hasDerivAt (hne t)).deriv]
  field_simp [hne t]

/-- Differentiating the quotient flux cancels the two first-derivative terms. -/
theorem quotient_flux_deriv {H F : ℝ → ℂ}
    (hH : ContDiff ℝ 2 H) (hF : ContDiff ℝ 2 F)
    (hne : ∀ t, H t ≠ 0) (t : ℝ) :
    deriv (fun s => H s ^ 2 * deriv (fun u => F u / H u) s) t =
      H t * deriv (deriv F) t - deriv (deriv H) t * F t := by
  have hdH : Differentiable ℝ H := hH.differentiable (by norm_num)
  have hdF : Differentiable ℝ F := hF.differentiable (by norm_num)
  have hdH' : Differentiable ℝ (deriv H) :=
    (contDiff_deriv_of_two hH).differentiable (by norm_num)
  have hdF' : Differentiable ℝ (deriv F) :=
    (contDiff_deriv_of_two hF).differentiable (by norm_num)
  have he : (fun s => H s ^ 2 * deriv (fun u => F u / H u) s) =
      (fun s => H s * deriv F s - deriv H s * F s) :=
    funext (quotient_flux_eq_wronskian hdH hdF hne)
  rw [he]
  rw [(((hdH t).hasDerivAt.fun_mul (hdF' t).hasDerivAt).fun_sub
    ((hdH' t).hasDerivAt.fun_mul (hdF t).hasDerivAt)).deriv]
  ring

namespace GaussianAnnularMode
variable {c : ℂ} {F : ℝ → ℂ} {l r : ℝ} (h : GaussianAnnularMode c F l r)
include h

theorem semicircleQuotient_left_endpoint : semicircleQuotient c F l = 0 := by
  simp [semicircleQuotient, h.left_endpoint]

theorem semicircleQuotient_right_endpoint : semicircleQuotient c F r = 0 := by
  simp [semicircleQuotient, h.right_endpoint]

/-- The actual mode-two Gaussian equation becomes a weighted divergence
identity with the positive gap `4-1=3`. -/
theorem semicircle_transformed_equation (t : ℝ) (ht : t ∈ Ioc l r) :
    deriv (fun s => semicircleProfile c s ^ 2 *
      deriv (semicircleQuotient c F) s) t =
      3 * semicircleProfile c t ^ 2 * semicircleQuotient c F t := by
  have hp : ContDiff ℝ 2 (semicircleProfile c) :=
    (semicircleProfile_smooth c).of_le (by simp)
  change deriv (fun s => semicircleProfile c s ^ 2 *
    deriv (fun u => F u / semicircleProfile c u) s) t = _
  rw [quotient_flux_deriv hp h.regularity
    (semicircleProfile_ne_zero h.upper_half_plane), semicircleProfile_second]
  have heq := h.equation t ht
  have hscale := congrArg (fun z : ℂ => (Real.exp t : ℂ) * z) heq
  have hquot := semicircleProfile_mul_quotient h.upper_half_plane F t
  unfold semicircleProfile at hscale ⊢ hquot
  linear_combination hscale - 3 * (Real.exp t : ℂ) *
    ((neutralOmega t : ℂ) - c) * hquot

end GaussianAnnularMode
end UnforcedLeray.Rayleigh
