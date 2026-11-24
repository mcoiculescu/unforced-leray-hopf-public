import UnforcedLeray.Analysis.Rayleigh.RealSpeed.Profile
import UnforcedLeray.Analysis.Sturm.NeutralPotentialRegularity
import Mathlib.Analysis.Calculus.DSlope

/-!
# Actual removal of a simple real critical denominator

The ratio is constructed from divided differences. At the critical point it
has the derivative-ratio value; elsewhere it equals ordinary scalar division
when numerator and denominator vanish at that point. Its continuity follows
from differentiability and a nonzero denominator derivative, with no assumed
removable-singularity conclusion. Generic real normed-space numerators include
both the real and complex Rayleigh fields.
-/

noncomputable section
open Set
open scoped ContDiff Topology
namespace UnforcedLeray.Rayleigh.RealSpeed
open Sturm GaussianPotential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The quotient with its actual derivative-ratio value at the critical point. -/
def removedQuotient (f : ℝ → E) (g : ℝ → ℝ) (a t : ℝ) : E :=
  (dslope g a t)⁻¹ • dslope f a t

@[simp] theorem removedQuotient_at_critical (f : ℝ → E) (g : ℝ → ℝ) (a : ℝ) :
    removedQuotient f g a a = (deriv g a)⁻¹ • deriv f a := by
  simp only [removedQuotient, dslope_same]

/-- Away from the critical point this is the literal quotient, including
ordinary totalized division at any other zero of the denominator. -/
theorem removedQuotient_eq_div {f : ℝ → E} {g : ℝ → ℝ} {a t : ℝ}
    (hf : f a = 0) (hg : g a = 0) (ht : t ≠ a) :
    removedQuotient f g a t = (g t)⁻¹ • f t := by
  unfold removedQuotient
  rw [dslope_of_ne g ht, dslope_of_ne f ht]
  simp only [slope, vsub_eq_sub, hf, hg, sub_zero, smul_eq_mul]
  simp only [mul_inv_rev, inv_inv, smul_smul, mul_assoc,
    mul_inv_cancel₀ (sub_ne_zero.mpr ht), mul_one]

/-- The extension is continuous at the actual simple zero. -/
theorem removedQuotient_continuousAt {f : ℝ → E} {g : ℝ → ℝ} {a : ℝ}
    (hf : DifferentiableAt ℝ f a) (hg : DifferentiableAt ℝ g a)
    (hd : deriv g a ≠ 0) : ContinuousAt (removedQuotient f g a) a := by
  have hdf : ContinuousAt (dslope f a) a := continuousAt_dslope_same.mpr hf
  have hdg : ContinuousAt (dslope g a) a := continuousAt_dslope_same.mpr hg
  exact (hdg.inv₀ (by simpa only [dslope_same] using hd)).smul hdf

theorem continuous_dslope_of_continuous_at {f : ℝ → E} {a : ℝ}
    (hf : Continuous f) (hfa : DifferentiableAt ℝ f a) : Continuous (dslope f a) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  by_cases ht : t = a
  · subst t
    exact continuousAt_dslope_same.mpr hfa
  · exact (continuousAt_dslope_of_ne ht).mpr hf.continuousAt

theorem dslope_ne_zero_of_unique_zero {g : ℝ → ℝ} {a : ℝ}
    (hga : g a = 0) (hd : deriv g a ≠ 0) (hz : ∀ t, t ≠ a → g t ≠ 0) (t : ℝ) :
    dslope g a t ≠ 0 := by
  by_cases ht : t = a
  · subst t
    simpa only [dslope_same] using hd
  · rw [dslope_of_ne g ht]
    simpa only [slope, vsub_eq_sub, hga, sub_zero, smul_eq_mul] using
      mul_ne_zero (inv_ne_zero (sub_ne_zero.mpr ht)) (hz t ht)

/-- If the denominator has only one simple zero, the concrete extended quotient
is globally continuous. No smooth-density or abstract quotient extension is used. -/
theorem removedQuotient_continuous {f : ℝ → E} {g : ℝ → ℝ} {a : ℝ}
    (hf : Continuous f) (hg : Continuous g)
    (hfa : DifferentiableAt ℝ f a) (hga : DifferentiableAt ℝ g a)
    (hgzero : g a = 0) (hd : deriv g a ≠ 0) (hz : ∀ t, t ≠ a → g t ≠ 0) :
    Continuous (removedQuotient f g a) := by
  exact ((continuous_dslope_of_continuous_at hg hga).inv₀
    (dslope_ne_zero_of_unique_zero hgzero hd hz)).smul
      (continuous_dslope_of_continuous_at hf hfa)

/-- The concrete Gaussian denominator at a real spectral speed. -/
def gaussianDenominator (c t : ℝ) : ℝ := neutralOmega t - c

theorem hasDerivAt_gaussianDenominator (c t : ℝ) :
    HasDerivAt (gaussianDenominator c) (-2 * neutralRadius t * neutralOmega t) t :=
  (hasDerivAt_neutralOmega t).sub_const c

theorem deriv_gaussianDenominator_neg (c t : ℝ) : deriv (gaussianDenominator c) t < 0 := by
  rw [(hasDerivAt_gaussianDenominator c t).deriv]
  exact mul_neg_of_neg_of_pos
    (mul_neg_of_neg_of_pos (by norm_num) (neutralRadius_pos t)) (neutralOmega_pos t)

/-- The concrete Gaussian quotient for a numerator vanishing at its critical point. -/
def gaussianRemovedQuotient (f : ℝ → E) (c a : ℝ) : ℝ → E :=
  removedQuotient f (gaussianDenominator c) a

theorem gaussianRemovedQuotient_continuous {f : ℝ → E} {c a : ℝ}
    (hf : ContDiff ℝ 1 f) (ha : neutralOmega a = c) :
    Continuous (gaussianRemovedQuotient f c a) := by
  apply removedQuotient_continuous hf.continuous (continuous_neutralOmega.sub continuous_const)
    (hf.differentiable (by norm_num) a) (hasDerivAt_gaussianDenominator c a).differentiableAt
  · exact sub_eq_zero.mpr ha
  · exact ne_of_lt (deriv_gaussianDenominator_neg c a)
  · intro t ht
    exact sub_ne_zero.mpr (fun h => ht (neutralOmega_injective (h.trans ha.symm)))

theorem gaussianRemovedQuotient_eq_div {f : ℝ → E} {c a t : ℝ}
    (hf : f a = 0) (ha : neutralOmega a = c) (ht : t ≠ a) :
    gaussianRemovedQuotient f c a t = (neutralOmega t - c)⁻¹ • f t :=
  removedQuotient_eq_div hf (sub_eq_zero.mpr ha) ht

/-- The exact critical value is supplied by the actual Gaussian derivative. -/
theorem gaussianRemovedQuotient_at_critical (f : ℝ → E) (c a : ℝ) :
    gaussianRemovedQuotient f c a a = (-2 * neutralRadius a * neutralOmega a)⁻¹ • deriv f a := by
  rw [gaussianRemovedQuotient, removedQuotient_at_critical,
    (hasDerivAt_gaussianDenominator c a).deriv]

/-- The continuous source to which the actual second derivative will be identified. -/
def gaussianRemovedSecondSource (f : ℝ → E) (c a : ℝ) (t : ℝ) : E :=
  (4 : ℝ) • f t + gaussianRayleighCoefficient t • gaussianRemovedQuotient f c a t

theorem gaussianCoefficient_continuous : Continuous gaussianRayleighCoefficient := by
  unfold gaussianRayleighCoefficient gaussianOffset
  exact continuous_Wlog.neg.mul (continuous_neutralOmega.sub continuous_const)

theorem gaussianRemovedSecondSource_continuous {f : ℝ → E} {c a : ℝ}
    (hf : ContDiff ℝ 1 f) (ha : neutralOmega a = c) :
    Continuous (gaussianRemovedSecondSource f c a) :=
  (continuous_const.smul hf.continuous).add
    (gaussianCoefficient_continuous.smul (gaussianRemovedQuotient_continuous hf ha))

/-- Away from the critical point the continuous source is the literal divided ODE. -/
theorem gaussianRemovedSecondSource_eq_div {f : ℝ → E} {c a t : ℝ}
    (hf : f a = 0) (ha : neutralOmega a = c) (ht : t ≠ a) :
    gaussianRemovedSecondSource f c a t = (4 : ℝ) • f t +
      (gaussianRayleighCoefficient t / (neutralOmega t - c)) • f t := by
  rw [gaussianRemovedSecondSource, gaussianRemovedQuotient_eq_div hf ha ht]
  simp only [smul_smul, div_eq_mul_inv]

end UnforcedLeray.Rayleigh.RealSpeed
