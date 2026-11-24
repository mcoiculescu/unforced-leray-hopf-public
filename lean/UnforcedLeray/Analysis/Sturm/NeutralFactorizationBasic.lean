import UnforcedLeray.Analysis.Sturm.QuadraticForm
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic

/-!
# The ground-state identity with an excluded zero

The denominator below need only be nonzero on the compact trial's topological
support. Integration by parts therefore remains valid when the reference
solution has zeros outside that support. All integrability statements are
proved before the integrals are compared.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set
open scoped ContDiff
namespace UnforcedLeray.Sturm

private theorem integrable_mul_compact_of_continuousOn {f a : ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f)
    (ha : ContinuousOn a (tsupport f)) : Integrable (fun t => a t * f t) := by
  apply (integrableOn_iff_integrable_of_support_subset
    ((Function.support_mul_subset_right a f).trans (subset_tsupport f))).mp
  exact (ha.mul hf.continuousOn).integrableOn_compact hfc

/-- The actual first-order expression appearing in the ground-state transform. -/
def groundStateSquare (h f : ℝ → ℝ) (t : ℝ) : ℝ :=
  (deriv f t - deriv h t / h t * f t) ^ 2

/-- Exact ground-state factorization on a compact trial away from the zeros of h.
No positivity, factorization or integral identity is supplied as a hypothesis. -/
theorem groundState_factorization {h f V : ℝ → ℝ}
    (hh : ContDiff ℝ ∞ h) (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f)
    (hzero : ∀ t ∈ tsupport f, h t ≠ 0)
    (hode : ∀ t ∈ tsupport f, deriv (deriv h) t = V t * h t)
    (hform : Integrable (fun t => deriv f t ^ 2 + V t * f t ^ 2)) :
    Integrable (groundStateSquare h f) ∧
      (∫ t, deriv f t ^ 2 + V t * f t ^ 2) = ∫ t, groundStateSquare h f t := by
  let r : ℝ → ℝ := fun t => deriv h t / h t
  let q : ℝ → ℝ := fun t =>
    (deriv (deriv h) t * h t - deriv h t ^ 2) / h t ^ 2
  have hdh : ContDiff ℝ ∞ (deriv h) := (contDiff_infty_iff_deriv.mp hh).2
  have hcr : ContinuousOn r (tsupport f) :=
    hdh.continuous.continuousOn.div hh.continuous.continuousOn hzero
  have hcq : ContinuousOn q (tsupport f) := by
    apply ContinuousOn.div
    · exact ((hdh.continuous_deriv (by simp)).continuousOn.mul
        hh.continuous.continuousOn).sub (hdh.continuous.continuousOn.pow 2)
    · exact hh.continuous.continuousOn.pow 2
    · intro t ht
      exact pow_ne_zero 2 (hzero t ht)
  have hderivr : ∀ t ∈ tsupport (fun x => f x ^ 2), HasDerivAt r (q t) t := by
    intro t ht
    have htf : t ∈ tsupport f := by
      exact (show tsupport (fun x => f x ^ 2) ⊆ tsupport f from
        by simpa only [pow_two] using (tsupport_mul_subset_left (f := f) (g := f))) ht
    have hquot := (hdh.differentiable (by simp) t).hasDerivAt.div
      (hh.differentiable (by simp) t).hasDerivAt (hzero t htf)
    convert hquot using 1
    all_goals first | rfl | simp [q, pow_two]
  have hderivf : ∀ t ∈ tsupport r,
      HasDerivAt (fun x => f x ^ 2) (2 * f t * deriv f t) t := by
    intro t _
    convert ((hf.differentiable (by simp) t).hasDerivAt.pow 2) using 1
    all_goals first | rfl | simp
  have hi1 : Integrable (fun t => r t * (2 * f t * deriv f t)) := by
    have hi := integrable_mul_compact_of_continuousOn hf.continuous hfc
      ((hcr.mul (continuousOn_const (c := (2 : ℝ)))).mul hf.continuous_deriv_one.continuousOn)
    convert hi using 1
    ext t
    change r t * (2 * f t * deriv f t) = ((r t * 2) * deriv f t) * f t
    ring
  have hi2 : Integrable (fun t => q t * f t ^ 2) := by
    have hi := integrable_mul_compact_of_continuousOn hf.continuous hfc
      (hcq.mul hf.continuous.continuousOn)
    simpa only [pow_two, mul_assoc, Pi.mul_apply] using hi
  have hi0 : Integrable (fun t => r t * f t ^ 2) := by
    have hi := integrable_mul_compact_of_continuousOn hf.continuous hfc
      (hcr.mul hf.continuous.continuousOn)
    simpa only [pow_two, mul_assoc, Pi.mul_apply] using hi
  have hibp : (∫ t, r t * (2 * f t * deriv f t)) = -(∫ t, q t * f t ^ 2) :=
    integral_mul_deriv_eq_deriv_mul_of_integrable hderivr hderivf hi1 hi2 hi0
  have hid (t : ℝ) : deriv f t ^ 2 + V t * f t ^ 2 =
      groundStateSquare h f t + q t * f t ^ 2 + r t * (2 * f t * deriv f t) := by
    by_cases ht : t ∈ tsupport f
    · have hr : q t + r t ^ 2 = V t := by
        dsimp [q, r]
        rw [hode t ht]
        field_simp [hzero t ht]
        <;> ring
      unfold groundStateSquare
      change deriv f t ^ 2 + V t * f t ^ 2 =
        (deriv f t - r t * f t) ^ 2 + q t * f t ^ 2 +
          r t * (2 * f t * deriv f t)
      rw [← hr]
      ring
    · have hz := image_eq_zero_of_notMem_tsupport ht
      simp [groundStateSquare, hz]
  have hiS : Integrable (groundStateSquare h f) := by
    have hi := (hform.sub hi2).sub hi1
    apply hi.congr
    filter_upwards [] with t
    change (deriv f t ^ 2 + V t * f t ^ 2 - q t * f t ^ 2) -
      r t * (2 * f t * deriv f t) = groundStateSquare h f t
    linarith [hid t]
  refine ⟨hiS, ?_⟩
  calc
    (∫ t, deriv f t ^ 2 + V t * f t ^ 2) =
        ∫ t, groundStateSquare h f t + q t * f t ^ 2 +
          r t * (2 * f t * deriv f t) := integral_congr_ae (Filter.Eventually.of_forall hid)
    _ = (∫ t, groundStateSquare h f t) + (∫ t, q t * f t ^ 2) +
          (∫ t, r t * (2 * f t * deriv f t)) := by
      rw [integral_add (hiS.fun_add hi2) hi1, integral_add hiS hi2]
    _ = ∫ t, groundStateSquare h f t := by rw [hibp]; ring

/-- Positivity is a consequence of the checked square factorization. -/
theorem groundState_form_nonneg {h f V : ℝ → ℝ}
    (hh : ContDiff ℝ ∞ h) (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f)
    (hzero : ∀ t ∈ tsupport f, h t ≠ 0)
    (hode : ∀ t ∈ tsupport f, deriv (deriv h) t = V t * h t)
    (hform : Integrable (fun t => deriv f t ^ 2 + V t * f t ^ 2)) :
    0 ≤ ∫ t, deriv f t ^ 2 + V t * f t ^ 2 := by
  rw [(groundState_factorization hh hf hfc hzero hode hform).2]
  exact integral_nonneg (fun t => sq_nonneg _)

end UnforcedLeray.Sturm
