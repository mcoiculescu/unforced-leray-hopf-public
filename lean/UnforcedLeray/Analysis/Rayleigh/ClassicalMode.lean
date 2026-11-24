import UnforcedLeray.Analysis.Rayleigh.LimitEquation
import UnforcedLeray.Analysis.Sturm.OneDRegularityH2
import UnforcedLeray.Analysis.Sturm.OneDRegularitySmooth
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Classical whole-line Gaussian Rayleigh modes

The actual undivided weak equation identifies the free Green source with a
continuous function when the spectral speed is in the upper half-plane.
Genuine weak free uniqueness and the proved classical Green kernel formulas
then yield C² regularity and the Rayleigh equation at every point. No classical
regularity, pointwise equation, or decay is assumed in this upgrade.
-/

noncomputable section
open MeasureTheory Set Filter
namespace UnforcedLeray.Rayleigh
open Sturm NonUniqueEuler.Sob

/-- A whole-line mode of the actual logarithmic Gaussian Rayleigh equation. -/
structure GaussianWholeLineMode (c : ℂ) (F : ℝ → ℂ) : Prop where
  upper_half_plane : 0 < c.im
  regularity : ContDiff ℝ 2 F
  memLp : MemLp F 2 volume
  deriv_memLp : MemLp (deriv F) 2 volume
  second_memLp : MemLp (deriv (deriv F)) 2 volume
  nonzero : ∃ t, F t ≠ 0
  equation : ∀ t,
    ((neutralOmega t : ℂ) - c) * (deriv (deriv F) t - 4 * F t) -
      (gaussianRayleighCoefficient t : ℂ) * F t = 0

/-- The actual continuous free Green source for an unstable speed. -/
def gaussianContinuousSource (c : ℂ) (F : ℝ → ℂ) (t : ℝ) : ℂ :=
  -((gaussianRayleighCoefficient t : ℂ) / ((neutralOmega t : ℂ) - c)) * F t

theorem gaussianSpeed_denominator_ne_zero {c : ℂ} (hc : 0 < c.im) (t : ℝ) :
    (neutralOmega t : ℂ) - c ≠ 0 := by
  intro hz
  have him := congrArg Complex.im hz
  simp only [Complex.sub_im, Complex.ofReal_im, Complex.zero_im, zero_sub] at him
  linarith

theorem continuous_gaussianContinuousSource {c : ℂ} (hc : 0 < c.im)
    {F : ℝ → ℂ} (hF : Continuous F) : Continuous (gaussianContinuousSource c F) :=
  (((Complex.continuous_ofReal.comp continuous_gaussianRayleighCoefficient).div
    ((Complex.continuous_ofReal.comp continuous_neutralOmega).sub continuous_const)
    (gaussianSpeed_denominator_ne_zero hc)).neg).mul hF

/-- The a.e. differential equation identifies this source with minus the
actual L² residual class. -/
theorem gaussianContinuousSource_ae {c : ℂ} (hc : 0 < c.im)
    {F : ℝ → ℂ} {u k : ComplexL2} (hFu : F =ᵐ[volume] (u : ℝ → ℂ))
    (heq : ∀ᵐ t ∂volume,
      ((neutralOmega t : ℂ) - c) * k t -
        (gaussianRayleighCoefficient t : ℂ) * u t = 0) :
    ((-k : ComplexL2) : ℝ → ℂ) =ᵐ[volume] gaussianContinuousSource c F := by
  filter_upwards [Lp.coeFn_neg k, hFu, heq] with t hk hF ht
  simp only [Pi.neg_apply] at hk
  rw [hk]
  unfold gaussianContinuousSource
  rw [hF]
  have hd := gaussianSpeed_denominator_ne_zero hc t
  have hkt : k t = (gaussianRayleighCoefficient t : ℂ) /
      ((neutralOmega t : ℂ) - c) * u t := by
    apply (mul_left_cancel₀ hd)
    calc
      ((neutralOmega t : ℂ) - c) * k t =
          (gaussianRayleighCoefficient t : ℂ) * u t := sub_eq_zero.mp ht
      _ = _ := by field_simp
  rw [hkt]
  ring

/-- Actual weak second derivatives recover the mass-two Green resolvent. -/
theorem weakGaussian_eq_freeResolvent {u k : ComplexL2}
    (hsecond : HasWeakDerivOn univ [1, 1] (u : ℝ → ℂ)
      ((k + (4 : ℂ) • u : ComplexL2) : ℝ → ℂ)) :
    freeResolventOperator (by norm_num : (0 : ℝ) < 2) (-k) = u := by
  have h := weakH2_eq_freeResolvent (by norm_num : (0 : ℝ) < 2)
    u (k + (4 : ℂ) • u) hsecond
  norm_num only [Complex.ofReal_ofNat, show (2 : ℂ) ^ 2 = 4 by norm_num] at h
  convert h using 1 <;> abel_nf

/-- The continuous representative equals the genuine Green integral everywhere. -/
theorem continuous_weakGaussian_eq_freeResolvent {c : ℂ} (hc : 0 < c.im)
    {F : ℝ → ℂ} (hF : Continuous F) {u k : ComplexL2}
    (hFu : F =ᵐ[volume] (u : ℝ → ℂ))
    (hsecond : HasWeakDerivOn univ [1, 1] (u : ℝ → ℂ)
      ((k + (4 : ℂ) • u : ComplexL2) : ℝ → ℂ))
    (heq : ∀ᵐ t ∂volume,
      ((neutralOmega t : ℂ) - c) * k t -
        (gaussianRayleighCoefficient t : ℂ) * u t = 0) :
    F = freeResolvent 2 (gaussianContinuousSource c F) := by
  have hrep := coeFn_freeResolventOperator (by norm_num : (0 : ℝ) < 2) (-k)
  rw [weakGaussian_eq_freeResolvent hsecond] at hrep
  have hraw : F = freeResolvent 2 ((-k : ComplexL2) : ℝ → ℂ) :=
    Measure.eq_of_ae_eq (hFu.trans hrep) hF
      (contDiff_one_freeResolvent_of_memLp (by norm_num) (Lp.memLp (-k))).continuous
  exact hraw.trans (freeResolvent_congr_ae 2 (gaussianContinuousSource_ae hc hFu heq))

/-- A nonzero genuine weak H² Gaussian mode at an unstable speed is a
classical whole-line mode, with both classical derivatives in actual L². -/
theorem gaussianWholeLineMode_of_weak {c : ℂ} (hc : 0 < c.im)
    {F : ℝ → ℂ} (hF : Continuous F) {u k : ComplexL2} (hu : u ≠ 0)
    (hFu : F =ᵐ[volume] (u : ℝ → ℂ))
    (hsecond : HasWeakDerivOn univ [1, 1] (u : ℝ → ℂ)
      ((k + (4 : ℂ) • u : ComplexL2) : ℝ → ℂ))
    (heq : ∀ᵐ t ∂volume,
      ((neutralOmega t : ℂ) - c) * k t -
        (gaussianRayleighCoefficient t : ℂ) * u t = 0) :
    GaussianWholeLineMode c F := by
  have hs : MemLp (gaussianContinuousSource c F) 2 volume :=
    (Lp.memLp (-k)).ae_eq (gaussianContinuousSource_ae hc hFu heq)
  have hsc := continuous_gaussianContinuousSource hc hF
  have hGreen := continuous_weakGaussian_eq_freeResolvent hc hF hFu hsecond heq
  have hreg : ContDiff ℝ 2 F := by
    rw [hGreen]
    exact contDiff_two_freeResolvent_of_memLp_continuous (by norm_num) hs hsc
  have hd : MemLp (deriv F) 2 volume := by
    rw [hGreen]
    exact memLp_deriv_freeResolvent_of_memLp (by norm_num) hs
  have hdd : MemLp (deriv (deriv F)) 2 volume := by
    rw [hGreen]
    exact memLp_deriv_two_freeResolvent_of_memLp_continuous (by norm_num) hs hsc
  have hder : deriv (deriv F) =
      fun t => (4 : ℂ) * F t - gaussianContinuousSource c F t := by
    conv_lhs => rw [hGreen]
    rw [deriv_freeResolvent_of_memLp (by norm_num : (0 : ℝ) < 2) hs,
      deriv_freeResolventDeriv_of_memLp_continuous (by norm_num : (0 : ℝ) < 2) hs hsc]
    rw [← hGreen]
    norm_num
  refine ⟨hc, hreg, (Lp.memLp u).ae_eq hFu.symm, hd, hdd, ?_, ?_⟩
  · by_contra hn
    push Not at hn
    apply hu
    apply Lp.eq_zero_iff_ae_eq_zero.mpr
    filter_upwards [hFu] with t ht
    simpa only [hn t, Pi.zero_apply] using ht.symm
  · intro t
    rw [hder]
    unfold gaussianContinuousSource
    have hden := gaussianSpeed_denominator_ne_zero hc t
    field_simp
    ring

end UnforcedLeray.Rayleigh
