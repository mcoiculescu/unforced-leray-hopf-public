import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.Bg.YoungW2.Corr.Sub
import UnforcedLeray.Cons.L2.SolAudit.ResumeConstruction.JointRepCellLp
import UnforcedLeray.Cons.L2.BackgroundConcrete.PhasePairingJointRep

/-!
# Integrability of a phase-test pairing over the slab (helper of `bgContRepWeakSlice`)
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.Cons.C03.Concrete

/-- The slab measure `(0,P] × ℝ³` is the restriction of the volume. -/
theorem slab_eq_restrict (P : ℝ) :
    ((volume : Measure ℝ).restrict (Ioc (0 : ℝ) P)).prod (volume : Measure Space) =
      (volume : Measure (ℝ × Space)).restrict (Ioc (0 : ℝ) P ×ˢ (univ : Set Space)) := by
  simpa only [Measure.volume_eq_prod] using
    (Measure.restrict_prod_eq_prod_univ (μ := (volume : Measure ℝ))
      (ν := (volume : Measure Space)) (Ioc 0 P))

theorem integrable_dotL_rep_slab {P : ℝ} [Fact (0 < P)] (w : Yq P UnforcedLeray.B0412.q0E)
    {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ) :
    Integrable (fun z : ℝ × Space => dotL (Φ z) (rep w z.1 z.2))
      (((volume : Measure ℝ).restrict (Ioc (0 : ℝ) P)).prod (volume : Measure Space)) := by
  set μS := ((volume : Measure ℝ).restrict (Ioc (0 : ℝ) P)).prod (volume : Measure Space) with hμS
  obtain ⟨R, hR⟩ := hΦ.bounded_support
  set B : Set (ℝ × Space) := univ ×ˢ Metric.closedBall (0 : Space) R with hB
  have hBm : MeasurableSet B := MeasurableSet.univ.prod Metric.isClosed_closedBall.measurableSet
  -- bound on the slab
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ τ ∈ Icc (0 : ℝ) P, ∀ y, ‖Φ (τ, y)‖ ≤ C := by
    have hK : IsCompact (Icc (0 : ℝ) P ×ˢ Metric.closedBall (0 : Space) (max R 0)) :=
      isCompact_Icc.prod (isCompact_closedBall _ _)
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hΦ.continuous.continuousOn
    refine ⟨max C 0, fun τ hτ y => ?_⟩
    by_cases hy : ‖y‖ ≤ max R 0
    · exact (hC (τ, y) ⟨hτ, by simpa using hy⟩).trans (le_max_left _ _)
    · rw [hR τ y (lt_of_le_of_lt (le_max_left _ _) (not_le.1 hy))]
      simp
  have hmem : MemLp (fun z : ℝ × Space => rep w z.1 z.2) UnforcedLeray.B0412.q0E μS := by
    rw [hμS, slab_eq_restrict]
    exact memLp_rep_periodCell UnforcedLeray.B0412.q0E_ne_top w
  have hfin : IsFiniteMeasure (μS.restrict B) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ, hB, hμS, Measure.prod_prod]
    simp only [Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (isCompact_closedBall (0 : Space) R).measure_lt_top
  have hRint : Integrable (fun z : ℝ × Space => rep w z.1 z.2) (μS.restrict B) :=
    (hmem.restrict B).integrable (Fact.out : (1 : ℝ≥0∞) ≤ UnforcedLeray.B0412.q0E)
  have hae : ∀ᵐ z ∂μS, z.1 ∈ Ioc (0 : ℝ) P := by
    rw [hμS, slab_eq_restrict]
    have := ae_restrict_mem (μ := (volume : Measure (ℝ × Space)))
      (measurableSet_Ioc.prod MeasurableSet.univ : MeasurableSet (Ioc (0 : ℝ) P ×ˢ (univ : Set Space)))
    filter_upwards [this] with z hz using hz.1
  have hmeas : AEStronglyMeasurable (fun z : ℝ × Space => dotL (Φ z) (rep w z.1 z.2)) μS := by
    have h1 : AEStronglyMeasurable (fun z : ℝ × Space => Φ z) μS :=
      hΦ.continuous.aestronglyMeasurable
    have h2 : AEStronglyMeasurable (fun z : ℝ × Space => rep w z.1 z.2) μS :=
      (stronglyMeasurable_rep w).aestronglyMeasurable
    exact (dotL : CVec3 →L[ℂ] CVec3 →L[ℂ] ℂ).aestronglyMeasurable_comp₂ h1 h2
  have hint : Integrable (fun z : ℝ × Space => dotL (Φ z) (rep w z.1 z.2)) (μS.restrict B) := by
    refine Integrable.mono' ((hRint.norm).const_mul (‖(dotL : CVec3 →L[ℂ] CVec3 →L[ℂ] ℂ)‖ * C))
      hmeas.restrict ?_
    filter_upwards [ae_restrict_of_ae hae] with z hz
    have h1 : ‖Φ z‖ ≤ C := hC z.1 (Ioc_subset_Icc_self hz) z.2
    calc ‖dotL (Φ z) (rep w z.1 z.2)‖
        ≤ ‖(dotL : CVec3 →L[ℂ] CVec3 →L[ℂ] ℂ)‖ * ‖Φ z‖ * ‖rep w z.1 z.2‖ :=
          (ContinuousLinearMap.le_opNorm₂ _ _ _)
      _ ≤ ‖(dotL : CVec3 →L[ℂ] CVec3 →L[ℂ] ℂ)‖ * C * ‖rep w z.1 z.2‖ := by
          gcongr
  have hsupp : Function.support (fun z : ℝ × Space => dotL (Φ z) (rep w z.1 z.2)) ⊆ B := by
    intro z hz
    refine ⟨mem_univ _, ?_⟩
    by_contra hy
    apply hz
    have : Φ z = 0 := hR z.1 z.2 (by simpa [Metric.mem_closedBall, dist_zero_right] using hy)
    simp [this]
  exact (integrableOn_iff_integrable_of_support_subset hsupp).mp hint

end UnforcedLeray.Short.PartIIIb.Concrete
