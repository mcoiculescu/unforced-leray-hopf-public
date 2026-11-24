import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
# The exact weighted-moment algebra behind the rotating semicircle

All three moments are finite integrals of actual continuous functions on a
finite interval. The integrated transformed ODE is used explicitly as a
hypothesis here; the Gaussian application proves it by integration by parts.
-/
noncomputable section
open MeasureTheory Set
namespace UnforcedLeray.Rayleigh

lemma semicircle_moment_expansion {w Ω : ℝ → ℝ} (hw : Continuous w) (hΩ : Continuous Ω)
    (c : ℂ) (l r : ℝ) :
    (∫ t in Ioc l r, (w t : ℂ) * ((Ω t : ℂ) - c) ^ 2) =
      ((∫ t in Ioc l r, w t * Ω t ^ 2 : ℝ) : ℂ) -
        (2 * c) * ((∫ t in Ioc l r, w t * Ω t : ℝ) : ℂ) +
        c ^ 2 * ((∫ t in Ioc l r, w t : ℝ) : ℂ) := by
  have hi0 : IntegrableOn (fun t => (w t : ℂ)) (Ioc l r) :=
    (Complex.continuous_ofReal.comp hw).integrableOn_Ioc
  have hi1 : IntegrableOn (fun t => ((w t * Ω t : ℝ) : ℂ)) (Ioc l r) :=
    (Complex.continuous_ofReal.comp (hw.mul hΩ)).integrableOn_Ioc
  have hi2 : IntegrableOn (fun t => ((w t * Ω t ^ 2 : ℝ) : ℂ)) (Ioc l r) :=
    (Complex.continuous_ofReal.comp (hw.mul (hΩ.pow 2))).integrableOn_Ioc
  have heq : (fun t => (w t : ℂ) * ((Ω t : ℂ) - c) ^ 2) =
      (fun t => ((w t * Ω t ^ 2 : ℝ) : ℂ) -
        (2 * c) * ((w t * Ω t : ℝ) : ℂ) + c ^ 2 * (w t : ℂ)) := by
    funext t
    push_cast
    ring
  rw [heq, integral_add (hi2.fun_sub (hi1.const_mul (2 * c))) (hi0.const_mul (c ^ 2)),
    integral_sub hi2 (hi1.const_mul (2 * c)), integral_const_mul, integral_const_mul,
    integral_complex_ofReal, integral_complex_ofReal, integral_complex_ofReal]

/-- The exact semicircle follows from a nonzero positive weighted moment,
without any spectral existence or compactness hypothesis. -/
theorem semicircle_of_weighted_moment_zero {w Ω : ℝ → ℝ}
    (hw : Continuous w) (hΩ : Continuous Ω) (hwn : ∀ t, 0 ≤ w t)
    (hΩn : ∀ t, 0 ≤ Ω t) (hΩle : ∀ t, Ω t ≤ 1)
    {c : ℂ} (hc : 0 < c.im) (l r : ℝ)
    (hmass : 0 < ∫ t in Ioc l r, w t)
    (hmoment : (∫ t in Ioc l r, (w t : ℂ) * ((Ω t : ℂ) - c) ^ 2) = 0) :
    (c.re - 1 / 2) ^ 2 + c.im ^ 2 ≤ 1 / 4 ∧ 0 < c.re ∧ c.re < 1 := by
  let A : ℝ := ∫ t in Ioc l r, w t
  let B : ℝ := ∫ t in Ioc l r, w t * Ω t
  let C : ℝ := ∫ t in Ioc l r, w t * Ω t ^ 2
  have hA : 0 < A := hmass
  rw [semicircle_moment_expansion hw hΩ] at hmoment
  change (C : ℂ) - (2 * c) * (B : ℂ) + c ^ 2 * (A : ℂ) = 0 at hmoment
  have hr := congrArg Complex.re hmoment
  have him := congrArg Complex.im hmoment
  norm_num [pow_two, Complex.mul_re, Complex.mul_im] at hr him
  have hcancel : c.im * (B - c.re * A) = 0 := by nlinarith [him]
  have hB : B = c.re * A :=
    sub_eq_zero.mp ((mul_eq_zero.mp hcancel).resolve_left hc.ne')
  have hC : C = (c.re ^ 2 + c.im ^ 2) * A := by rw [hB] at hr; nlinarith [hr]
  have hCB : C ≤ B := by
    apply integral_mono
      ((hw.mul (hΩ.pow 2)).integrableOn_Ioc)
      ((hw.mul hΩ).integrableOn_Ioc)
    intro t
    apply mul_le_mul_of_nonneg_left _ (hwn t)
    change Ω t ^ 2 ≤ Ω t
    have hp := mul_nonneg (hΩn t) (sub_nonneg.mpr (hΩle t))
    nlinarith
  rw [hC, hB] at hCB
  have hbound : c.re ^ 2 + c.im ^ 2 ≤ c.re := (mul_le_mul_iff_left₀ hA).mp hCB
  have him2 : 0 < c.im ^ 2 := sq_pos_of_pos hc
  refine ⟨by nlinarith, by nlinarith [sq_nonneg c.re], ?_⟩
  by_contra hbad
  have hre : 1 ≤ c.re := le_of_not_gt hbad
  have hp := mul_nonneg (le_trans (by norm_num : (0 : ℝ) ≤ 1) hre)
    (sub_nonneg.mpr hre)
  nlinarith

end UnforcedLeray.Rayleigh
