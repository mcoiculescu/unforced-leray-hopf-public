import UnforcedLeray.Short.PartI.Sub.C09
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Helper for `polarReduction`: smooth angular integrals `r ↦ ∫_{-π}^{π} f(r, θ) dθ`

For a smooth `f : ℝ × ℝ → ℂ`, the function `Φ_f(r) = ∫_{-π}^{π} f(r, θ) dθ` is `C^∞` and
`Φ_f'(r) = ∫_{-π}^{π} ∂₁f(r, θ) dθ`, where `∂₁ f = Df (1, 0)` (`dsl f`).  These are the
differentiation-under-the-integral facts used for the angular mode `e^{2iθ} φ(r cos θ, r sin θ)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Real
open scoped ContDiff

namespace UnforcedLeray.Short.PartI.PolarRed

/-- The radial partial derivative `∂₁ f (p) = Df(p) (1, 0)` of `f : ℝ × ℝ → ℂ`. -/
def dsl (f : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ := fderiv ℝ f p (1, 0)

theorem contDiff_dsl {f : ℝ × ℝ → ℂ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (dsl f) :=
  (ContDiff.fderiv_right (m := ∞) hf (by simp)).clm_apply contDiff_const

theorem hasDerivAt_slice {f : ℝ × ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (r θ : ℝ) :
    HasDerivAt (fun s : ℝ => f (s, θ)) (dsl f (r, θ)) r := by
  have hpair : HasDerivAt (fun s : ℝ => (s, θ)) ((1 : ℝ), (0 : ℝ)) r :=
    (hasDerivAt_id' r).prodMk (hasDerivAt_const r θ)
  exact (hf.differentiable (by simp) (r, θ)).hasFDerivAt.comp_hasDerivAt r hpair

/-- Differentiation under the integral sign for the angular integral over `[-π, π]`. -/
theorem hasDerivAt_param {f : ℝ × ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (x₀ : ℝ) :
    HasDerivAt (fun r : ℝ => ∫ θ in (-π)..π, f (r, θ))
      (∫ θ in (-π)..π, dsl f (x₀, θ)) x₀ := by
  have hd : Continuous (dsl f) := (contDiff_dsl hf).continuous
  obtain ⟨M, hM⟩ := ((isCompact_closedBall x₀ 1).prod
      (isCompact_Icc (a := -π) (b := π))).exists_bound_of_continuousOn hd.continuousOn
  have hcont : ∀ r : ℝ, Continuous (fun θ : ℝ => f (r, θ)) := fun r =>
    hf.continuous.comp (Continuous.prodMk continuous_const continuous_id)
  have hπ : -π ≤ π := by linarith [Real.pi_pos]
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun r θ => f (r, θ)) (F' := fun r θ => dsl f (r, θ)) (x₀ := x₀)
    (s := Metric.ball x₀ 1) (bound := fun _ => M)
    (Metric.ball_mem_nhds x₀ one_pos) ?_ ?_ ?_ ?_ ?_ ?_).2
  · exact Filter.Eventually.of_forall fun r => (hcont r).aestronglyMeasurable
  · exact (hcont x₀).intervalIntegrable _ _
  · exact (hd.comp (Continuous.prodMk continuous_const continuous_id)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun t ht x hx => ?_
    rw [Set.uIoc_of_le hπ] at ht
    exact hM (x, t) ⟨Metric.ball_subset_closedBall hx, Ioc_subset_Icc_self ht⟩
  · exact intervalIntegrable_const
  · refine Filter.Eventually.of_forall fun t _ x _ => hasDerivAt_slice hf x t

/-- All finite orders of smoothness of `Φ_f`, by induction on the order. -/
theorem contDiff_param (n : ℕ) : ∀ {f : ℝ × ℝ → ℂ}, ContDiff ℝ ∞ f →
    ContDiff ℝ n (fun r : ℝ => ∫ θ in (-π)..π, f (r, θ)) := by
  induction n with
  | zero =>
    intro f hf
    rw [Nat.cast_zero, contDiff_zero]
    exact continuous_iff_continuousAt.2 fun x => (hasDerivAt_param hf x).continuousAt
  | succ n ih =>
    intro f hf
    rw [show ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 by push_cast; rfl,
      contDiff_succ_iff_deriv]
    refine ⟨fun x => (hasDerivAt_param hf x).differentiableAt, fun h => ?_, ?_⟩
    · exact absurd h (by simp)
    · have hderiv : deriv (fun r : ℝ => ∫ θ in (-π)..π, f (r, θ)) =
          fun r : ℝ => ∫ θ in (-π)..π, dsl f (r, θ) := by
        funext x
        exact (hasDerivAt_param hf x).deriv
      rw [hderiv]
      exact ih (contDiff_dsl hf)

/-- The angular integral `Φ_f(r) = ∫_{-π}^{π} f(r, θ) dθ` of a smooth `f` is smooth. -/
theorem contDiff_param_infty {f : ℝ × ℝ → ℂ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun r : ℝ => ∫ θ in (-π)..π, f (r, θ)) :=
  contDiff_infty.2 fun n => contDiff_param n hf

end UnforcedLeray.Short.PartI.PolarRed
