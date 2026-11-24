import UnforcedLeray.Infra.VolterraEvolution.Strip

/-!
# Short-time comparison with the free evolution

On the strip, `E(τ,s) - S₀(τ - s)` is the Volterra integral of `E(·,s)`, hence of size
`O((τ - s)^{1/2})`:

`‖E(τ,s) - S₀(τ - s)‖ ≤ 2 C₀ β (2 M₀ e^λ) (τ - s)^{1/2}`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology intervalIntegral Real

namespace UnforcedLeray.Infra.VolterraEvolution

namespace VolterraData

variable {𝕜 : Type*} [RCLike 𝕜] {X Y : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [NormedSpace ℝ X] [SMulCommClass ℝ 𝕜 X]
  [CompleteSpace X] (D : VolterraData 𝕜 X Y)

/-- Pointwise square-root estimate for the Volterra correction on the strip. -/
theorem norm_stripEvolution_sub_apply_le {s τ : ℝ} (hτ : τ ∈ Icc s (s + 1)) (x : X) :
    ‖D.stripEvolution τ s x - D.S₀ (τ - s) x‖ ≤
      2 * D.C₀ * D.β * D.stripBound * (τ - s) ^ (1 / 2 : ℝ) * ‖x‖ := by
  rw [D.stripEvolution_eq hτ x, add_sub_cancel_left]
  have hM : 0 ≤ D.stripBound * ‖x‖ := mul_nonneg D.stripBound_nonneg (norm_nonneg _)
  have hg : IntervalIntegrable (fun r => D.C₀ * D.β * (τ - r) ^ (-(1 / 2 : ℝ)) *
      (D.stripBound * ‖x‖)) volume s τ :=
    ((intervalIntegrable_kernel τ s τ).const_mul (D.C₀ * D.β)).mul_const _
  refine (norm_integral_le_of_norm_le hτ.1 ?_ hg).trans (le_of_eq ?_)
  · filter_upwards [ae_ne_real τ] with r hrτ hr
    have hr' : r ∈ Ico s τ := ⟨hr.1.le, lt_of_le_of_ne hr.2 hrτ⟩
    refine (D.norm_integrand_le hτ.2 hr' (fun r => D.stripEvolution r s x)).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (mul_nonneg D.C₀_nonneg D.β_nonneg)
      (rpow_nonneg (by linarith [hr'.2]) _))
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (D.norm_stripEvolution_le r s) (norm_nonneg _))
  · rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul, integral_kernel]
    ring

/-- Operator-norm form: `‖E(τ,s) - S₀(τ - s)‖ ≤ 2 C₀ β (2 M₀ e^λ) (τ - s)^{1/2}`. -/
theorem norm_stripEvolution_sub_le {s τ : ℝ} (hτ : τ ∈ Icc s (s + 1)) :
    ‖D.stripEvolution τ s - D.S₀ (τ - s)‖ ≤
      2 * D.C₀ * D.β * D.stripBound * (τ - s) ^ (1 / 2 : ℝ) := by
  have h0 : 0 ≤ 2 * D.C₀ * D.β * D.stripBound * (τ - s) ^ (1 / 2 : ℝ) := by
    have := D.C₀_nonneg; have := D.β_nonneg; have := D.stripBound_nonneg
    have : 0 ≤ (τ - s) ^ (1 / 2 : ℝ) := rpow_nonneg (by linarith [hτ.1]) _
    positivity
  refine ContinuousLinearMap.opNorm_le_bound _ h0 fun x => ?_
  rw [ContinuousLinearMap.sub_apply]
  exact D.norm_stripEvolution_sub_apply_le hτ x

end VolterraData

end UnforcedLeray.Infra.VolterraEvolution
