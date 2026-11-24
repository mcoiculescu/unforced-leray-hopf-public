import UnforcedLeray.Units.B0449.GraphSpaceTime

/-!
# The fixed temporal cutoff for the B0449 resolvent argument

This cutoff is one on a neighborhood of the observation time and is supported strictly inside
the unit chart strip. Its derivative has the same support property, so every graph test remains
inside the single strip controlled by `chart_norm_le`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.B0449

/-- A smooth time cutoff equal to one on `[-1/8,1/8]` and supported in `(-1/4,1/4)`. -/
def resolventTimeBump : ContDiffBump (0 : ℝ) := ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩

/-- The scalar function underlying the fixed time cutoff. -/
def resolventTimeCutoff : ℝ → ℝ := resolventTimeBump

/-- The time derivative of the fixed cutoff. -/
def resolventTimeCutoffDeriv (t : ℝ) : ℝ := fderiv ℝ resolventTimeCutoff t 1

theorem contDiff_resolventTimeCutoff : ContDiff ℝ ∞ resolventTimeCutoff :=
  resolventTimeBump.contDiff

theorem resolventTimeCutoff_eq_one {t : ℝ} (ht : |t| ≤ 1 / 8) :
    resolventTimeCutoff t = 1 := by
  apply resolventTimeBump.one_of_mem_closedBall
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
  exact ht

theorem resolventTimeCutoff_eq_zero {t : ℝ} (ht : 1 / 4 ≤ |t|) :
    resolventTimeCutoff t = 0 := by
  apply resolventTimeBump.zero_of_le_dist
  rw [dist_zero_right, Real.norm_eq_abs]
  exact ht

theorem hasCompactSupport_resolventTimeCutoff : HasCompactSupport resolventTimeCutoff :=
  resolventTimeBump.hasCompactSupport

theorem hasCompactSupport_resolventTimeCutoffDeriv :
    HasCompactSupport resolventTimeCutoffDeriv := by
  exact hasCompactSupport_resolventTimeCutoff.fderiv_apply ℝ 1

theorem continuous_resolventTimeCutoff : Continuous resolventTimeCutoff :=
  contDiff_resolventTimeCutoff.continuous

theorem continuous_resolventTimeCutoffDeriv : Continuous resolventTimeCutoffDeriv := by
  exact (contDiff_resolventTimeCutoff.continuous_fderiv (by norm_num)).clm_apply
    continuous_const

/-- The cutoff and its derivative have finite global suprema. -/
theorem exists_resolventTimeCutoff_bounds :
    ∃ Mχ Mχt : ℝ, 0 ≤ Mχ ∧ 0 ≤ Mχt ∧
      (∀ t, ‖(resolventTimeCutoff t : ℂ)‖ ≤ Mχ) ∧
      (∀ t, ‖(resolventTimeCutoffDeriv t : ℂ)‖ ≤ Mχt) := by
  obtain ⟨Mχ, hχ⟩ :=
    hasCompactSupport_resolventTimeCutoff.exists_bound_of_continuous
      continuous_resolventTimeCutoff
  obtain ⟨Mχt, hχt⟩ :=
    hasCompactSupport_resolventTimeCutoffDeriv.exists_bound_of_continuous
      continuous_resolventTimeCutoffDeriv
  refine ⟨max 0 Mχ, max 0 Mχt, le_max_left _ _, le_max_left _ _, ?_, ?_⟩
  · intro t
    simpa only [Complex.norm_real] using (hχ t).trans (le_max_right _ _)
  · intro t
    simpa only [Complex.norm_real] using (hχt t).trans (le_max_right _ _)

theorem resolventTimeCutoff_zero_outside_unitStrip {t : ℝ}
    (ht : t ∉ Ioo (-(1 / 2 : ℝ)) (1 / 2)) : resolventTimeCutoff t = 0 := by
  apply resolventTimeCutoff_eq_zero
  by_cases hleft : t ≤ -(1 / 2 : ℝ)
  · rw [abs_of_nonpos (by linarith)]
    linarith
  · have hright : (1 / 2 : ℝ) ≤ t := by
      by_contra hn
      exact ht ⟨by linarith, lt_of_not_ge hn⟩
    rw [abs_of_nonneg (by linarith)]
    linarith

theorem resolventTimeCutoffDeriv_zero_outside_unitStrip {t : ℝ}
    (ht : t ∉ Ioo (-(1 / 2 : ℝ)) (1 / 2)) : resolventTimeCutoffDeriv t = 0 := by
  rw [resolventTimeCutoffDeriv, fderiv_of_notMem_tsupport]
  · rfl
  · rw [show resolventTimeCutoff = resolventTimeBump from rfl,
      resolventTimeBump.tsupport_eq]
    intro hball
    apply ht
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at hball
    norm_num [resolventTimeBump] at hball
    rcases abs_le.mp hball with ⟨hneg, hpos⟩
    exact ⟨by linarith, by linarith⟩

end UnforcedLeray.B0449
