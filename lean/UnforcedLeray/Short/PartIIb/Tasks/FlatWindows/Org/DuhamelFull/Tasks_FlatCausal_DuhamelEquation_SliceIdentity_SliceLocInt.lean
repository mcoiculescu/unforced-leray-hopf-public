import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.DuhamelFull.Defs
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelEquation.SliceIdentity.SliceLocInt
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.DuhamelFull.Sub_PartIIb_T12_7_6

/-!
# Part II-b, task `PartII-b:T12/7/6/4` (`dfe_deqSliceLocInt`): local integrability of a slice pairing

Source of record: `the November 2 reference manuscript`, lines 1923-1927.
A planar slice `g` that is a.e. `c`-periodic with finite `L^r` cell norm is `L^r` on every strip
`[-M, M] × [-N, N]` (finitely many translated cells), hence `L^1` there; multiply by a bounded
compactly supported test.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb

/-- **Task `PartII-b:T12/7/6/4`** (SP 1923-1927). -/
theorem dfe_deqSliceLocInt : UnforcedLeray.Short.IIb.dfe_DeqSliceLocInt := by
  intro c r t g hc hr hg Ψ hΨ i
  have hr0 : 0 < r := by linarith
  have hcont : Continuous (fun x : Coord => Ψ x i) := (hΨ.smooth i).smooth.continuous
  set ψ : ℝ × ℝ → ℝ := fun z => Ψ (t, z) i with hψ
  have hψc : Continuous ψ := hcont.comp (Continuous.prodMk continuous_const continuous_id)
  have hK : IsCompact (Prod.snd '' tsupport (fun x : Coord => Ψ x i)) :=
    (hΨ.smooth i).compact.isCompact.image continuous_snd
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : ℝ × ℝ)
  have hsupp : Function.support (fun z : ℝ × ℝ => g z i * (ψ z : ℂ)) ⊆
      Icc (-R) R ×ˢ Icc (-R) R := by
    intro z hz
    have hz1 : ψ z ≠ 0 := by
      intro h0
      apply hz
      simp [h0]
    have hmem : z ∈ Prod.snd '' tsupport (fun x : Coord => Ψ x i) :=
      ⟨(t, z), subset_tsupport _ hz1, rfl⟩
    have := hR hmem
    rw [mem_closedBall_zero_iff] at this
    have h1 : |z.1| ≤ R := (norm_fst_le z).trans this
    have h2 : |z.2| ≤ R := (norm_snd_le z).trans this
    simp only [mem_prod, mem_Icc]
    exact ⟨abs_le.1 h1, abs_le.1 h2⟩
  obtain ⟨C, hC⟩ : ∃ C, ∀ z, ‖ψ z‖ ≤ C := by
    have hcs : HasCompactSupport ψ := by
      refine HasCompactSupport.of_support_subset_isCompact hK ?_
      intro z hz
      exact ⟨(t, z), subset_tsupport _ hz, rfl⟩
    exact hψc.bounded_above_of_compact_support hcs
  set box : Set (ℝ × ℝ) := Icc (-R) R ×ˢ Icc (-R) R with hbox
  have hboxc : IsCompact box := isCompact_Icc.prod isCompact_Icc
  haveI : IsFiniteMeasure ((volume : Measure (ℝ × ℝ)).restrict box) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hboxc.measure_lt_top⟩
  have hmeas : AEStronglyMeasurable g ((volume : Measure (ℝ × ℝ)).restrict box) :=
    hg.2.1.restrict
  have hlp : MemLp g (ENNReal.ofReal r) ((volume : Measure (ℝ × ℝ)).restrict box) := by
    refine ⟨hmeas, ?_⟩
    have hp0 : ENNReal.ofReal r ≠ 0 := by simpa using hr0
    have hpt : ENNReal.ofReal r ≠ ⊤ := ENNReal.ofReal_ne_top
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt, ENNReal.toReal_ofReal hr0.le]
    exact ENNReal.rpow_lt_top_of_nonneg (by positivity) (ds_box_lt_top hc hr hg R R).ne
  have hint : Integrable g ((volume : Measure (ℝ × ℝ)).restrict box) :=
    (hlp.mono_exponent (p := 1) (by
      rw [ENNReal.one_le_ofReal]; exact hr.le)).integrable le_rfl
  have hon : IntegrableOn (fun z : ℝ × ℝ => g z i * (ψ z : ℂ)) box := by
    refine Integrable.mono' (g := fun z => ‖g z‖ * C) (hint.norm.mul_const C) ?_ ?_
    · exact (((EuclideanSpace.proj i : CMerid →L[ℂ] ℂ).continuous.comp_aestronglyMeasurable
        hmeas)).mul (Complex.continuous_ofReal.comp hψc).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun z => ?_
      rw [norm_mul]
      refine mul_le_mul (PiLp.norm_apply_le (g z) i) ?_ (norm_nonneg _) (norm_nonneg _)
      simpa using hC z
  exact (integrableOn_iff_integrable_of_support_subset hsupp).1 hon

end UnforcedLeray.Short.IIb
