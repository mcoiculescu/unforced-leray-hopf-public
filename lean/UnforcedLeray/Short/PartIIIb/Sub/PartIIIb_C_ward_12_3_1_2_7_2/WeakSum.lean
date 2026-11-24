import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_7_2
import UnforcedLeray.Cons.L2.BackgroundConcrete.RepresentativeLp
import UnforcedLeray.Cons.L2.BackgroundConcrete.PhasePairF

/-!
# `gEQWeakSum` (source 2525-2531): weak derivatives add

Phase tests are bounded and vanish for large `y`, so the four products are integrable on the
cell; `phaseInt` is additive on integrable pieces (Fubini, `integral_prod`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace MeasureTheory Set
open UnforcedLeray.Cons.C03.Concrete (Params rep pairF phaseInt)

/-- A phase test is bounded on `ℝ × ℝ³`. -/
theorem wsum_phase_bdd {P : ℝ} [Fact (0 < P)] {ψ : ℝ × UnforcedLeray.Space → ℂ}
    (hψ : IsPhaseTest P ψ) : ∃ A : ℝ, ∀ x, ‖ψ x‖ ≤ A := by
  obtain ⟨R, hR⟩ := hψ.bounded_support
  obtain ⟨C, hC⟩ := ((isCompact_Icc (a := (0 : ℝ)) (b := P)).prod
    (isCompact_closedBall (0 : UnforcedLeray.Space) R)).exists_bound_of_continuousOn
      hψ.continuous.continuousOn
  refine ⟨max C 0, fun x => ?_⟩
  obtain ⟨τ, y⟩ := x
  by_cases hy : R < ‖y‖
  · rw [hR τ y hy]
    simp
  · push_neg at hy
    have hper : Function.Periodic (fun t : ℝ => ψ (t, y)) P := fun t => hψ.periodic t y
    obtain ⟨t, ht, hτ⟩ := hper.exists_mem_Ico₀ (Fact.out : (0 : ℝ) < P) τ
    have hb := hC (t, y) ⟨⟨ht.1, ht.2.le⟩, mem_closedBall_zero_iff.2 hy⟩
    have hτ' : ψ (τ, y) = ψ (t, y) := hτ
    rw [hτ']
    exact le_trans hb (le_max_left _ _)

theorem wsum_cell_fin (P : ℝ) [Fact (0 < P)] (R : ℝ) :
    IsFiniteMeasure (((volume.restrict (Ioc (0 : ℝ) P)).prod
      (volume : Measure UnforcedLeray.Space)).restrict
        (univ ×ˢ Metric.closedBall (0 : UnforcedLeray.Space) R)) := by
  constructor
  rw [Measure.restrict_apply_univ, Measure.prod_prod, Measure.restrict_apply_univ]
  exact ENNReal.mul_lt_top measure_Ioc_lt_top measure_closedBall_lt_top

theorem wsum_int_bdd (P : ℝ) [Fact (0 < P)] (R : ℝ) {g : ℝ × UnforcedLeray.Space → ℂ}
    (hc : Continuous g) (C : ℝ) (hC : ∀ x, ‖g x‖ ≤ C) :
    Integrable g (((volume.restrict (Ioc (0 : ℝ) P)).prod
      (volume : Measure UnforcedLeray.Space)).restrict
        (univ ×ˢ Metric.closedBall (0 : UnforcedLeray.Space) R)) := by
  have := wsum_cell_fin P R
  exact Integrable.of_bound hc.aestronglyMeasurable C (ae_of_all _ hC)

theorem wsum_int_Lq (P : ℝ) [Fact (0 < P)] (R : ℝ) {g : ℝ × UnforcedLeray.Space → ℂ}
    (hg : MemLp g UnforcedLeray.B0412.q0E
      ((volume.restrict (Ioc (0 : ℝ) P)).prod (volume : Measure UnforcedLeray.Space))) :
    Integrable g (((volume.restrict (Ioc (0 : ℝ) P)).prod
      (volume : Measure UnforcedLeray.Space)).restrict
        (univ ×ˢ Metric.closedBall (0 : UnforcedLeray.Space) R)) := by
  have := wsum_cell_fin P R
  exact (hg.restrict _).integrable (Fact.out : (1 : ENNReal) ≤ UnforcedLeray.B0412.q0E)

/-- A continuous bounded `a` vanishing for large `y` times an integrable `g` on the restricted
cell is integrable on the cell. -/
theorem wsum_int_mul {P : ℝ} [Fact (0 < P)] {R : ℝ} {a g : ℝ × UnforcedLeray.Space → ℂ}
    (ha : Continuous a) (hasupp : ∀ (τ : ℝ) (y : UnforcedLeray.Space), R < ‖y‖ → a (τ, y) = 0)
    (A : ℝ) (hA : ∀ x, ‖a x‖ ≤ A)
    (hg : Integrable g (((volume.restrict (Ioc (0 : ℝ) P)).prod
      (volume : Measure UnforcedLeray.Space)).restrict
        (univ ×ˢ Metric.closedBall (0 : UnforcedLeray.Space) R))) :
    Integrable (fun x => a x * g x)
      ((volume.restrict (Ioc (0 : ℝ) P)).prod (volume : Measure UnforcedLeray.Space)) := by
  have hSm : MeasurableSet (univ ×ˢ Metric.closedBall (0 : UnforcedLeray.Space) R) :=
    (MeasurableSet.univ (α := ℝ)).prod Metric.isClosed_closedBall.measurableSet
  have h1 : Integrable (fun x => a x * g x)
      (((volume.restrict (Ioc (0 : ℝ) P)).prod (volume : Measure UnforcedLeray.Space)).restrict
        (univ ×ˢ Metric.closedBall (0 : UnforcedLeray.Space) R)) :=
    Integrable.bdd_mul hg ha.aestronglyMeasurable (ae_of_all _ hA)
  have h2 : (fun x => a x * g x) = (univ ×ˢ Metric.closedBall (0 : UnforcedLeray.Space) R).indicator
      (fun x => a x * g x) := by
    funext x
    by_cases hx : x ∈ univ ×ˢ Metric.closedBall (0 : UnforcedLeray.Space) R
    · rw [Set.indicator_of_mem hx]
    · have hy : R < ‖x.2‖ := by
        have hx' := hx
        simp only [Set.mem_prod, Set.mem_univ, true_and, not_le] at hx'
        rw [Metric.mem_closedBall, dist_zero_right, not_le] at hx'
        exact hx'
      rw [Set.indicator_of_notMem hx, hasupp x.1 x.2 hy, zero_mul]
  rw [h2]
  exact (integrable_indicator_iff hSm).2 h1

/-- Additivity of the phase integral on integrable pieces. -/
theorem wsum_phaseInt_add {P : ℝ} [Fact (0 < P)] (f g : ℝ × UnforcedLeray.Space → ℂ)
    (hf : Integrable f ((volume.restrict (Ioc (0 : ℝ) P)).prod
      (volume : Measure UnforcedLeray.Space)))
    (hg : Integrable g ((volume.restrict (Ioc (0 : ℝ) P)).prod
      (volume : Measure UnforcedLeray.Space))) :
    phaseInt P (fun x => f x + g x) = phaseInt P f + phaseInt P g := by
  have hfg : Integrable (fun x => f x + g x)
      ((volume.restrict (Ioc (0 : ℝ) P)).prod (volume : Measure UnforcedLeray.Space)) :=
    Integrable.add hf hg
  unfold phaseInt
  rw [← integral_prod (fun x => f x + g x) hfg, ← integral_prod f hf, ← integral_prod g hg,
    integral_add hf hg, smul_add]

theorem gEQWeakSum : GEQWeakSum := by
  intro P _ j e e' r r' he he' hr hr' H1 H2 φ hφ
  have hd : IsPhaseTest P (dy j φ) := hφ.dy j
  obtain ⟨Rφ, hRφ⟩ := hφ.bounded_support
  obtain ⟨Rd, hRd⟩ := hd.bounded_support
  obtain ⟨Aφ, hAφ⟩ := wsum_phase_bdd hφ
  obtain ⟨Ad, hAd⟩ := wsum_phase_bdd hd
  obtain ⟨Ce, hCe⟩ := he.2
  obtain ⟨Ce', hCe'⟩ := he'.2
  have I1 : Integrable (fun x => dy j φ x * e x)
      ((volume.restrict (Ioc (0 : ℝ) P)).prod (volume : Measure UnforcedLeray.Space)) :=
    wsum_int_mul hd.continuous hRd Ad hAd
      (wsum_int_bdd P Rd he.1 Ce hCe)
  have I2 := wsum_int_mul hd.continuous hRd Ad hAd (wsum_int_Lq P Rd hr)
  have I3 := wsum_int_mul hφ.continuous hRφ Aφ hAφ (wsum_int_bdd P Rφ he'.1 Ce' hCe')
  have I4 := wsum_int_mul hφ.continuous hRφ Aφ hAφ (wsum_int_Lq P Rφ hr')
  have E1 := H1 φ hφ
  have E2 := H2 φ hφ
  have s1 : phaseInt P (fun x => dy j φ x * (e x + r x)) =
      phaseInt P (fun x => dy j φ x * e x) + phaseInt P (fun x => dy j φ x * r x) := by
    simp only [mul_add]
    exact wsum_phaseInt_add _ _ I1 I2
  have s2 : phaseInt P (fun x => φ x * (e' x + r' x)) =
      phaseInt P (fun x => φ x * e' x) + phaseInt P (fun x => φ x * r' x) := by
    simp only [mul_add]
    exact wsum_phaseInt_add _ _ I3 I4
  rw [s1, s2, E1, E2]
  ring

end UnforcedLeray.Short.PartIIIb.Concrete
