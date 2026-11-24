import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.OuterGen.Transp.Deriv.Defs

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set

namespace UnforcedLeray.Short.PartIIIb.NearInst

open UnforcedLeray.Short.PartIIIb.Concrete UnforcedLeray.Cons.C03.Concrete
  UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.B0220 (HSpace measureH Profile)
open UnforcedLeray.B0223 (MeridC)

theorem odExists : OD_Exists := by
  unfold OD_Exists
  intro p f hf
  have hP : 0 < p.period := p.period_pos
  obtain ⟨R, hR⟩ := hf.bounded_support
  have hKc : IsCompact (Icc (0 : ℝ) p.period ×ˢ Metric.closedBall (0 : Space) R) :=
    isCompact_Icc.prod (isCompact_closedBall _ _)
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hf.smooth.continuous.continuousOn
  have hbound : ∀ w : ℝ × Space, ‖f w‖ ≤ max C 0 := by
    rintro ⟨τ, y⟩
    by_cases hy : R < ‖y‖
    · rw [hR τ y hy, norm_zero]
      exact le_max_right _ _
    · have hper : Function.Periodic (fun s => f (s, y)) p.period :=
        fun s => hf.periodic s y
      obtain ⟨τ', hτ', heq⟩ := hper.exists_mem_Ico₀ hP τ
      have hmem : (τ', y) ∈ Icc (0 : ℝ) p.period ×ˢ Metric.closedBall (0 : Space) R :=
        ⟨Ico_subset_Icc_self hτ', by simpa using not_lt.mp hy⟩
      have heq' : f (τ, y) = f (τ', y) := heq
      rw [heq']
      exact (hC _ hmem).trans (le_max_left _ _)
  set S : Set (UnforcedLeray.B0223.PSpace p.period) := {z | ‖z.1‖ ≤ R} with hSdef
  have hSm : MeasurableSet S :=
    measurableSet_le (measurable_norm.comp measurable_fst) measurable_const
  have hSfin : volume S < ⊤ := by
    have hEq : S = Metric.closedBall (0 : Space) R ×ˢ (univ : Set (AddCircle p.period)) := by
      ext z
      simp [hSdef]
    rw [hEq, Measure.volume_eq_prod, Measure.prod_prod]
    exact ENNReal.mul_lt_top measure_closedBall_lt_top (measure_lt_top _ _)
  set g : UnforcedLeray.B0223.PSpace p.period → CVec3 := fun z =>
    f ((UnforcedLeray.B0223.toCell p.period z).2,
      (UnforcedLeray.B0223.toCell p.period z).1) with hgdef
  have hgmeas : Measurable g := by
    refine hf.smooth.continuous.measurable.comp ?_
    exact (measurable_snd.comp (UnforcedLeray.B0223.measurable_toCell (P := p.period))).prodMk
      (measurable_fst.comp (UnforcedLeray.B0223.measurable_toCell (P := p.period)))
  have hgind : g = S.indicator g := by
    funext z
    by_cases hz : z ∈ S
    · rw [indicator_of_mem hz]
    · rw [indicator_of_notMem hz]
      have h1 : R < ‖z.1‖ := by
        have h2 := hz
        simp only [hSdef, mem_ofPred_eq, not_le] at h2
        exact h2
      exact hR _ _ h1
  have hmemS : MemLp (S.indicator g) 2 volume := by
    rw [memLp_indicator_iff_restrict hSm]
    have : IsFiniteMeasure (volume.restrict S) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hSfin⟩
    exact MemLp.of_bound hgmeas.aestronglyMeasurable (max C 0)
      (Filter.Eventually.of_forall fun z => hbound _)
  have hmemg : MemLp g 2 volume := by
    rw [hgind]
    exact hmemS
  refine ⟨hmemg.toLp g, ?_⟩
  unfold OuterRepFn
  exact MemLp.coeFn_toLp hmemg

end UnforcedLeray.Short.PartIIIb.NearInst
