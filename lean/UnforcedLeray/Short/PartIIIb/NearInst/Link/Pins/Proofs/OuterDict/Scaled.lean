import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_pins_3_4_2_2

/-!
# `OuterScaled` (task `PartIII-b:C/near/pins/3/4/2/2/1`)

Source `shorter-proof-2026-11-02.tex` lines 3289-3311. For a smooth, periodic, compactly supported
phase test `Φ`, the scaled field `Ψ(x,τ) = Φ(τ, x/ε)` is bounded and supported in the set
`{‖x‖ ≤ ε R}` (`R` from `bounded_support`), which has finite measure on `ℝ³ × ℝ/Pℤ`.
Hence it lies in `L²` and its `Lp` class is an element of `X`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set

namespace UnforcedLeray.Short.PartIIIb.NearInst

open UnforcedLeray.Short.PartIIIb.Concrete UnforcedLeray.Cons.C03.Concrete
  UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.B0220 (HSpace measureH Profile)
open UnforcedLeray.B0223 (MeridC)

theorem outerScaled : OuterScaled := by
  intro p Φ hΦ
  have hP : 0 < p.period := p.period_pos
  have hε : 0 < p.ε := p.ε_pos
  obtain ⟨R, hR⟩ := hΦ.bounded_support
  -- a uniform bound: Φ is continuous on the compact `[0,P] × closedBall 0 R`
  have hKc : IsCompact (Icc (0 : ℝ) p.period ×ˢ Metric.closedBall (0 : Space) R) :=
    isCompact_Icc.prod (isCompact_closedBall _ _)
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hΦ.smooth.continuous.continuousOn
  have hbound : ∀ w : ℝ × Space, ‖Φ w‖ ≤ max C 0 := by
    rintro ⟨τ, y⟩
    by_cases hy : R < ‖y‖
    · rw [hR τ y hy, norm_zero]
      exact le_max_right _ _
    · have hper : Function.Periodic (fun s => Φ (s, y)) p.period :=
        fun s => hΦ.periodic s y
      obtain ⟨τ', hτ', heq⟩ := hper.exists_mem_Ico₀ hP τ
      have hmem : (τ', y) ∈ Icc (0 : ℝ) p.period ×ˢ Metric.closedBall (0 : Space) R :=
        ⟨Ico_subset_Icc_self hτ', by simpa using not_lt.mp hy⟩
      have heq' : Φ (τ, y) = Φ (τ', y) := heq
      rw [heq']
      exact (hC _ hmem).trans (le_max_left _ _)
  -- the support set `{‖x‖ ≤ ε R}` and its finite measure
  set S : Set (UnforcedLeray.B0223.PSpace p.period) := {z | ‖z.1‖ ≤ p.ε * R} with hSdef
  have hSm : MeasurableSet S :=
    measurableSet_le (measurable_norm.comp measurable_fst) measurable_const
  have hSfin : volume S < ⊤ := by
    have hEq : S = Metric.closedBall (0 : Space) (p.ε * R) ×ˢ
        (univ : Set (AddCircle p.period)) := by
      ext z
      simp [hSdef]
    rw [hEq, Measure.volume_eq_prod, Measure.prod_prod]
    exact ENNReal.mul_lt_top measure_closedBall_lt_top (measure_lt_top _ _)
  set g : UnforcedLeray.B0223.PSpace p.period → CVec3 := fun z =>
    Φ ((UnforcedLeray.B0223.toCell p.period z).2,
      p.ε⁻¹ • (UnforcedLeray.B0223.toCell p.period z).1) with hgdef
  have hgmeas : Measurable g := by
    refine hΦ.smooth.continuous.measurable.comp ?_
    exact (measurable_snd.comp (UnforcedLeray.B0223.measurable_toCell (P := p.period))).prodMk
      ((continuous_const_smul p.ε⁻¹).measurable.comp
        (measurable_fst.comp (UnforcedLeray.B0223.measurable_toCell (P := p.period))))
  have hgind : g = S.indicator g := by
    funext z
    by_cases hz : z ∈ S
    · rw [indicator_of_mem hz]
    · rw [indicator_of_notMem hz]
      have h1 : p.ε * R < ‖z.1‖ := by
        have h2 := hz
        simp only [hSdef, mem_ofPred_eq, not_le] at h2
        exact h2
      have hz' : R < ‖p.ε⁻¹ • (UnforcedLeray.B0223.toCell p.period z).1‖ := by
        rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hε.le)]
        have h3 : p.ε⁻¹ * (p.ε * R) < p.ε⁻¹ * ‖z.1‖ :=
          mul_lt_mul_of_pos_left h1 (inv_pos.mpr hε)
        rw [← mul_assoc, inv_mul_cancel₀ hε.ne', one_mul] at h3
        exact h3
      exact hR _ _ hz'
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
  unfold OuterRep
  exact MemLp.coeFn_toLp hmemg

end UnforcedLeray.Short.PartIIIb.NearInst
