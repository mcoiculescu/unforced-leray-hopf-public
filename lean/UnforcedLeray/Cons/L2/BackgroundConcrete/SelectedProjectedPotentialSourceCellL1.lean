import UnforcedLeray.Cons.L2.BackgroundConcrete.SpatialProductBounds

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace UnforcedLeray.Cons.C03.Concrete

open UnforcedLeray.PhaseSpace

/-- A smooth phase-periodic scalar source with one common compact spatial support radius has a
uniform spatial L¹ bound on a compact period interval. -/
theorem exists_uniform_spatialL1_of_isPhaseTest {P : ℝ} [Fact (0 < P)]
    {f : SpaceTime → ℝ} (hf : IsPhaseTest P f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ ∈ Icc (0 : ℝ) P, ∫ y, |f (τ, y)| ≤ C := by
  obtain ⟨R, hR⟩ := hf.bounded_support
  let S : ℝ := max R 0
  have hS : 0 ≤ S := le_max_right _ _
  have hK : IsCompact (Icc (0 : ℝ) P ×ˢ Metric.closedBall (0 : Space) S) :=
    isCompact_Icc.prod (isCompact_closedBall _ _)
  obtain ⟨C, hC0, hC⟩ := exists_norm_bound_on_compact f hf.continuous hK
  have hBall : Integrable ((Metric.closedBall (0 : Space) S).indicator
      (fun _ : Space => C)) volume :=
    IntegrableOn.integrable_indicator
      (integrableOn_const (μ := volume) (s := Metric.closedBall (0 : Space) S)
        measure_closedBall_lt_top.ne)
      Metric.isClosed_closedBall.measurableSet
  refine ⟨C * volume.real (Metric.closedBall (0 : Space) S),
    mul_nonneg hC0 measureReal_nonneg, ?_⟩
  intro τ hτ
  have hslice : IsSpatialTest (fun y : Space => f (τ, y)) := by
    refine ⟨hf.smooth.comp (contDiff_const.prodMk contDiff_id), hf.hasCompactSupport_slice τ⟩
  have hleft : Integrable (fun y : Space => |f (τ, y)|) volume := hslice.integrable.abs
  have hright : Integrable ((Metric.closedBall (0 : Space) S).indicator
      (fun _ : Space => C)) volume := hBall
  have hdom : ∀ᵐ y ∂volume, |f (τ, y)| ≤
      (Metric.closedBall (0 : Space) S).indicator (fun _ : Space => C) y := by
    filter_upwards [] with y
    by_cases hy : ‖y‖ ≤ S
    · have hbound : ‖f (τ, y)‖ ≤ C := by
        apply hC (τ, y)
        exact ⟨hτ, by simpa [Metric.mem_closedBall, dist_zero_right] using hy⟩
      rw [Real.norm_eq_abs] at hbound
      have hyball : y ∈ Metric.closedBall (0 : Space) S := by
        simpa [Metric.mem_closedBall, dist_zero_right] using hy
      rw [Set.indicator_of_mem hyball]
      exact hbound
    · have hfar : R < ‖y‖ := lt_of_le_of_lt (le_max_left R 0) (lt_of_not_ge hy)
      have hzero : f (τ, y) = 0 := hR τ y hfar
      have hnot : y ∉ Metric.closedBall (0 : Space) S := by
        simpa [Metric.mem_closedBall, dist_zero_right] using hy
      rw [Set.indicator_of_notMem hnot]
      simp [hzero]
  have hInt := integral_mono_ae hleft hright hdom
  calc
    ∫ y, |f (τ, y)| ≤ ∫ y, (Metric.closedBall (0 : Space) S).indicator
        (fun _ : Space => C) y := hInt
    _ = volume.real (Metric.closedBall (0 : Space) S) • C :=
      integral_indicator_const C Metric.isClosed_closedBall.measurableSet
    _ = C * volume.real (Metric.closedBall (0 : Space) S) := by
      rw [smul_eq_mul]
      ring

#print axioms exists_uniform_spatialL1_of_isPhaseTest

end UnforcedLeray.Cons.C03.Concrete

end
