import UnforcedLeray.Cons.L2.BackgroundConcrete.SpatialProductHilbert

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace UnforcedLeray.Cons.C03.Concrete

/-- A jointly measurable scalar field with compact spatial support and a uniform bound belongs
to every finite-exponent `L^p` space on one phase cell. -/
theorem memLp_on_phaseCell_of_spatialSupport {P R : ℝ} {p : ℝ≥0∞}
    [Fact (0 < P)] [Fact (1 ≤ p)] (hp : p ≠ ⊤) {f : SpaceTime → ℂ}
    (hf : AEStronglyMeasurable f volume)
    (hbound : ∃ C : ℝ, ∀ z ∈ Icc (0 : ℝ) P ×ˢ Metric.closedBall (0 : Space) R,
      ‖f z‖ ≤ C)
    (hzero : ∀ τ ∈ Ioc (0 : ℝ) P, ∀ y : Space, R < ‖y‖ → f (τ, y) = 0) :
    MemLp f p (volume.restrict (phaseCell P)) := by
  let K : Set SpaceTime := Icc (0 : ℝ) P ×ˢ Metric.closedBall (0 : Space) R
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_closedBall _ _)
  have hKm : MeasurableSet K := hK.measurableSet
  obtain ⟨C, hC⟩ := hbound
  haveI : IsFiniteMeasure (volume.restrict K) :=
    isFiniteMeasure_restrict.mpr (hK.measure_lt_top.ne)
  have hmemK : MemLp (K.indicator f) p volume := by
    rw [memLp_indicator_iff_restrict hKm]
    exact MemLp.of_bound hf.restrict C
      (ae_restrict_of_forall_mem hKm fun z hz => hC z (by simpa [K] using hz))
  have hmemCell : MemLp (K.indicator f) p (volume.restrict (phaseCell P)) :=
    hmemK.mono_measure Measure.restrict_le_self
  have hae : f =ᵐ[volume.restrict (phaseCell P)] K.indicator f := by
    filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod MeasurableSet.univ)] with z hz
    by_cases hy : ‖z.2‖ ≤ R
    · have hzK : z ∈ K := by
        simp only [K, mem_prod, mem_Icc, Metric.mem_closedBall, dist_zero_right]
        exact ⟨⟨le_of_lt hz.1.1, hz.1.2⟩, hy⟩
      simp [Set.indicator_of_mem hzK]
    · have hfar : R < ‖z.2‖ := lt_of_not_ge hy
      have hfz : f z = 0 := hzero z.1 hz.1 z.2 hfar
      have hzK : z ∉ K := by
        simp only [K, mem_prod, mem_Icc, Metric.mem_closedBall, dist_zero_right]
        exact fun hzK => hy hzK.2
      simp [Set.indicator_of_notMem hzK, hfz]
  exact MemLp.ae_eq hae.symm hmemCell

#print axioms memLp_on_phaseCell_of_spatialSupport

end UnforcedLeray.Cons.C03.Concrete
