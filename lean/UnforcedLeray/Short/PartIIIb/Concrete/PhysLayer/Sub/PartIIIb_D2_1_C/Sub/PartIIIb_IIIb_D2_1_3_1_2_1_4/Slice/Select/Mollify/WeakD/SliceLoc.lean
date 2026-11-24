import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjMollLocInt

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped ContDiff
namespace UnforcedLeray.Short.PartIIIb.Concrete
open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- For a field `Φ` in `Y_2`, for almost every phase `τ` the slice `y ↦ Φ(τ, y)` is locally
integrable on `ℝ³` (Fubini on compact boxes of `ℝ × ℝ³` from `locInt_of_isInYr`). -/
theorem convYW_ae_locInt {P : ℝ} (hP : 0 < P) {Φ : ℝ × Space → CVec3}
    (hΦ : UnforcedLeray.Short.IIb.IsInYr P 2 Φ) :
    ∀ᵐ τ : ℝ, LocallyIntegrable (fun y : Space => Φ (τ, y)) volume := by
  have hL : LocallyIntegrable Φ volume := locInt_of_isInYr hP hΦ
  have key : ∀ p : ℕ × ℕ, ∀ᵐ τ : ℝ,
      τ ∈ Icc (-(p.1 : ℝ)) (p.1 : ℝ) →
        IntegrableOn (fun y : Space => Φ (τ, y)) (Metric.closedBall (0 : Space) (p.2 : ℝ)) volume := by
    intro p
    have hS : IsCompact (Icc (-(p.1 : ℝ)) (p.1 : ℝ) ×ˢ Metric.closedBall (0 : Space) (p.2 : ℝ)) :=
      isCompact_Icc.prod (isCompact_closedBall _ _)
    have hint : IntegrableOn Φ (Icc (-(p.1 : ℝ)) (p.1 : ℝ) ×ˢ Metric.closedBall (0 : Space) (p.2 : ℝ))
        volume := hL.integrableOn_isCompact hS
    have h2 : Integrable ((Icc (-(p.1 : ℝ)) (p.1 : ℝ) ×ˢ Metric.closedBall (0 : Space) (p.2 : ℝ)).indicator Φ)
        (volume.prod volume) := by
      rw [← Measure.volume_eq_prod]
      exact (integrable_indicator_iff hS.measurableSet).2 hint
    have h3 := h2.prod_right_ae
    filter_upwards [h3] with τ hτI hτ
    have hfun : (fun y : Space => (Icc (-(p.1 : ℝ)) (p.1 : ℝ) ×ˢ Metric.closedBall (0 : Space) (p.2 : ℝ)).indicator Φ (τ, y))
        = (Metric.closedBall (0 : Space) (p.2 : ℝ)).indicator (fun y : Space => Φ (τ, y)) := by
      funext y
      by_cases hy : y ∈ Metric.closedBall (0 : Space) (p.2 : ℝ)
      · simp [Set.indicator_of_mem, hy, hτ]
      · simp [Set.indicator_of_notMem, hy]
    rw [hfun] at hτI
    exact (integrable_indicator_iff Metric.isClosed_closedBall.measurableSet).1 hτI
  have hall : ∀ᵐ τ : ℝ, ∀ p : ℕ × ℕ, τ ∈ Icc (-(p.1 : ℝ)) (p.1 : ℝ) →
      IntegrableOn (fun y : Space => Φ (τ, y)) (Metric.closedBall (0 : Space) (p.2 : ℝ)) volume :=
    ae_all_iff.2 key
  filter_upwards [hall] with τ hτ
  rw [locallyIntegrable_iff]
  intro K hK
  obtain ⟨M, hM⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Space)).mp hK.isBounded
  obtain ⟨R, hR⟩ := exists_nat_ge M
  obtain ⟨N, hN⟩ := exists_nat_ge |τ|
  have hτN : τ ∈ Icc (-(N : ℝ)) (N : ℝ) := by
    constructor
    · have := neg_abs_le τ
      linarith
    · have := le_abs_self τ
      linarith
  exact (hτ (N, R) hτN).mono_set (hM.trans (Metric.closedBall_subset_closedBall hR))

end UnforcedLeray.Short.PartIIIb.Concrete
