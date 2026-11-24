import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T12_1_3_1_5

/-!
# Leaf `T12/1/3/1/5/2`: differentiation of the reflected mollification of a test

Proves `testMollDeriv : TestMollDeriv` (SP 1670, 1923-1926). Differentiation under the integral
(`hasFDerivAt_integral_of_dominated_of_fderiv_le`): the integrand `ρ(a) φ(u + a)` has derivative
`ρ(a) ∂φ(u + a)` in `u`, dominated on the unit ball around `u` by `C |ρ(a)|`, where `C` bounds
`∂φ` on the closed ball of radius `1 + rOut` (continuous on a compact set). Evaluation at `v`
commutes with the Bochner integral (`ContinuousLinearMap.integral_apply`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Complex
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

theorem testMollDeriv : UnforcedLeray.Short.IIb.TestMollDeriv := by
  intro c ρ φ hφ u v
  have hdiff : Differentiable ℝ φ := hφ.smooth.differentiable (by simp)
  have hcont : Continuous (fderiv ℝ φ) := hφ.smooth.continuous_fderiv (by simp)
  obtain ⟨C, hC⟩ : ∃ C, ∀ x ∈ Metric.closedBall u (1 + ρ.rOut), ‖fderiv ℝ φ x‖ ≤ C :=
    (isCompact_closedBall u (1 + ρ.rOut)).exists_bound_of_continuousOn hcont.continuousOn
  have hsupp : ∀ a : ℝ × ℝ, ρ.normed volume a ≠ 0 → ‖a‖ < ρ.rOut := by
    intro a ha
    have hmem : a ∈ Function.support (ρ.normed volume) := ha
    rwa [ContDiffBump.support_normed_eq, mem_ball_zero_iff] at hmem
  have hsmρ : ContDiff ℝ ∞ (ρ.normed volume) := ρ.contDiff_normed
  have hcontρ : Continuous (ρ.normed volume) := hsmρ.continuous
  have hint_bound : Integrable (fun a : ℝ × ℝ => C * ‖ρ.normed volume a‖) volume :=
    (hcontρ.integrable_of_hasCompactSupport ρ.hasCompactSupport_normed).norm.const_mul C
  -- the integrand and its derivative
  let F : ℝ × ℝ → ℝ × ℝ → ℝ := fun x a => ρ.normed volume a * φ (x + a)
  let F' : ℝ × ℝ → ℝ × ℝ → (ℝ × ℝ →L[ℝ] ℝ) := fun x a => ρ.normed volume a • fderiv ℝ φ (x + a)
  have hbound : ∀ a : ℝ × ℝ, ∀ x ∈ Metric.ball u 1,
      ‖F' x a‖ ≤ C * ‖ρ.normed volume a‖ := by
    intro a x hx
    by_cases ha : ρ.normed volume a = 0
    · simp [F, F', ha]
    · have hxu : ‖x - u‖ < 1 := by
        have := mem_ball_iff_norm.mp hx
        simpa using this
      have hxK : x + a ∈ Metric.closedBall u (1 + ρ.rOut) := by
        rw [Metric.mem_closedBall, dist_eq_norm]
        have e : x + a - u = (x - u) + a := by abel
        rw [e]
        have := norm_add_le (x - u) a
        have := hsupp a ha
        linarith
      show ‖ρ.normed volume a • fderiv ℝ φ (x + a)‖ ≤ C * ‖ρ.normed volume a‖
      rw [norm_smul, mul_comm C]
      exact mul_le_mul_of_nonneg_left (hC _ hxK) (norm_nonneg _)
  have hcontF : ∀ x, Continuous (F x) := fun x =>
    hcontρ.mul (hφ.smooth.continuous.comp (continuous_const.add continuous_id))
  have hcontF' : ∀ x, Continuous (F' x) := fun x => by
    show Continuous fun a : ℝ × ℝ => ρ.normed volume a • fderiv ℝ φ (x + a)
    exact hcontρ.smul (hcont.comp (continuous_const.add continuous_id))
  have hF_int : Integrable (F u) volume := by
    refine (hcontF u).integrable_of_hasCompactSupport ?_
    exact ρ.hasCompactSupport_normed.mul_right
  have hF'_int : Integrable (F' u) volume := by
    refine Integrable.mono' hint_bound (hcontF' u).aestronglyMeasurable ?_
    exact Eventually.of_forall fun a => hbound a u (Metric.mem_ball_self one_pos)
  have hF_diff : ∀ a : ℝ × ℝ, ∀ x : ℝ × ℝ, HasFDerivAt (fun x => F x a) (F' x a) x := by
    intro a x
    have h1 : HasFDerivAt φ (fderiv ℝ φ (x + a)) (x + a) := (hdiff (x + a)).hasFDerivAt
    have h2 : HasFDerivAt (fun x : ℝ × ℝ => x + a) (ContinuousLinearMap.id ℝ (ℝ × ℝ)) x :=
      (hasFDerivAt_id x).add_const a
    have h3 : HasFDerivAt (fun x => φ (x + a))
        ((fderiv ℝ φ (x + a)).comp (ContinuousLinearMap.id ℝ (ℝ × ℝ))) x := h1.comp x h2
    rw [ContinuousLinearMap.comp_id] at h3
    exact h3.const_mul (ρ.normed volume a)
  have hmain := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := volume) (F := F) (F' := F')
    (x₀ := u) (s := Metric.ball u 1) (bound := fun a : ℝ × ℝ => C * ‖ρ.normed volume a‖)
    (Metric.ball_mem_nhds u one_pos)
    (Eventually.of_forall fun x => (hcontF x).aestronglyMeasurable) hF_int
    (hcontF' u).aestronglyMeasurable
    (Eventually.of_forall fun a x hx => hbound a x hx) hint_bound
    (Eventually.of_forall fun a x _ => hF_diff a x)
  have htm : testMoll ρ φ = fun x => ∫ a, F x a := rfl
  rw [htm, hmain.fderiv, ContinuousLinearMap.integral_apply hF'_int v]
  simp [F', smul_eq_mul]

end UnforcedLeray.Short.IIb
