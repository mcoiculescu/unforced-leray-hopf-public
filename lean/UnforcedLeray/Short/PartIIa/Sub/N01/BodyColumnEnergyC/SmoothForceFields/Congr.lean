import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_9_1_2

/-!
# `PartII-a:N01/9/1/2/2`: `velFAeCongr`

`velF c u` reads `u` through the recentring `cellPtInv`, which is the identity on `0 < q` and a
translation by `(0, c, 0)` on `q ≤ 0`. A `measureH`-null exceptional set is volume-null on the cell
(`weightH` is positive there), translation invariance of `volume` handles the shifted half, and
`ageμ c a ≪ volume` transfers the conclusion to the age measure.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set Filter Topology
open UnforcedLeray.Short.PartIIIb.NearInst.Delta (velF)

namespace UnforcedLeray.Short.PartIIa.N01

/-- Null sets of `measureH c` are volume-null on the cell. -/
theorem measureH_ae_volume {c : ℝ} {P : UnforcedLeray.B0220.Profile → Prop}
    (h : ∀ᵐ p ∂UnforcedLeray.B0220.measureH c, P p) :
    ∀ᵐ p ∂(volume : Measure UnforcedLeray.B0220.Profile),
      p ∈ UnforcedLeray.B0220.cell c → P p := by
  have hcell : MeasurableSet (UnforcedLeray.B0220.cell c) :=
    measurableSet_Ioi.prod (measurableSet_Ioc.prod MeasurableSet.univ)
  unfold UnforcedLeray.B0220.measureH UnforcedLeray.B0220.cellMeasure at h
  rw [ae_withDensity_iff UnforcedLeray.B0220.measurable_weightH,
    ae_restrict_iff' hcell] at h
  filter_upwards [h] with p hp hmem
  have hpos : 0 < p.1 := hmem.1
  refine hp hmem ?_
  unfold UnforcedLeray.B0220.weightH
  exact (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos hpos _)).ne'

/-- The recentred cell point lies in the profile cell. -/
theorem cellPtInv_mem_cell {c : ℝ} (hc : 0 < c) {x : ℝ × (ℝ × ℝ)} (hs : 0 < x.1)
    (hq : x.2.1 ∈ Ico (-c / 2) (c / 2)) :
    UnforcedLeray.Short.PartIIIb.NearInst.Masked.cellPtInv c x ∈ UnforcedLeray.B0220.cell c := by
  obtain ⟨hq1, hq2⟩ := hq
  by_cases h0 : 0 < x.2.1
  · unfold UnforcedLeray.Short.PartIIIb.NearInst.Masked.cellPtInv
    rw [if_pos h0]
    exact ⟨hs, ⟨h0, by linarith⟩, trivial⟩
  · unfold UnforcedLeray.Short.PartIIIb.NearInst.Masked.cellPtInv
    rw [if_neg h0]
    exact ⟨hs, ⟨by linarith, by linarith [not_lt.1 h0]⟩, trivial⟩

/-- Absolute continuity of the age measure with respect to volume (as in `PartII-b`). -/
theorem ageμ_ac_volume' (c a : ℝ) : ageμ c a ≪ (volume : Measure (ℝ × (ℝ × ℝ))) := by
  rw [ageμ, Measure.volume_eq_prod]
  refine Measure.AbsolutelyContinuous.prod ?_ ?_
  · exact (withDensity_absolutelyContinuous _ _).trans
      (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
  · unfold Cyl.avgμ
    exact (Measure.smul_absolutelyContinuous).trans
      (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)

theorem velFAeCongr : UnforcedLeray.Short.PartIIa.N01.VelFAeCongr := by
  intro c hc u v huv
  have hN : ∀ᵐ p ∂UnforcedLeray.B0220.measureH c, u p = v p := huv
  have hV := measureH_ae_volume hN
  -- the exceptional set on the cell, volume-null
  have hZ := ae_iff.1 hV
  -- translated exceptional set, volume-null
  have hT : volume {x : ℝ × (ℝ × ℝ) | ¬ ((x.1, (x.2.1 + c, x.2.2)) ∈ UnforcedLeray.B0220.cell c →
      u (x.1, (x.2.1 + c, x.2.2)) = v (x.1, (x.2.1 + c, x.2.2)))} = 0 := by
    have : (volume : Measure (ℝ × (ℝ × ℝ))).IsAddRightInvariant := by
      rw [Measure.volume_eq_prod]; infer_instance
    have key : ∀ x : ℝ × (ℝ × ℝ), x + ((0 : ℝ), ((c : ℝ), (0 : ℝ))) =
        (x.1, (x.2.1 + c, x.2.2)) := by
      intro x
      exact Prod.ext (by simp) (Prod.ext (by simp) (by simp))
    have hset : {x : ℝ × (ℝ × ℝ) | ¬ ((x.1, (x.2.1 + c, x.2.2)) ∈ UnforcedLeray.B0220.cell c →
        u (x.1, (x.2.1 + c, x.2.2)) = v (x.1, (x.2.1 + c, x.2.2)))} =
        (fun x : ℝ × (ℝ × ℝ) => x + ((0 : ℝ), ((c : ℝ), (0 : ℝ)))) ⁻¹'
          {p : UnforcedLeray.B0220.Profile | ¬ (p ∈ UnforcedLeray.B0220.cell c → u p = v p)} := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_preimage, key]
    rw [hset, measure_preimage_add_right]
    exact hZ
  have hgood : ∀ᵐ x ∂(volume : Measure (ℝ × (ℝ × ℝ))),
      x ∈ Ioi (0 : ℝ) ×ˢ qCell c →
        u (UnforcedLeray.Short.PartIIIb.NearInst.Masked.cellPtInv c x) =
          v (UnforcedLeray.Short.PartIIIb.NearInst.Masked.cellPtInv c x) := by
    rw [ae_iff]
    have hS1 : volume {x : ℝ × (ℝ × ℝ) | 0 < x.2.1 ∧
        x ∈ {p : UnforcedLeray.B0220.Profile | ¬ (p ∈ UnforcedLeray.B0220.cell c → u p = v p)}} = 0 :=
      measure_mono_null (fun x hx => hx.2) hZ
    have hS2 : volume {x : ℝ × (ℝ × ℝ) | ¬ (0 < x.2.1) ∧
        (x.1, (x.2.1 + c, x.2.2)) ∈
          {p : UnforcedLeray.B0220.Profile | ¬ (p ∈ UnforcedLeray.B0220.cell c → u p = v p)}} = 0 :=
      measure_mono_null (fun x hx => hx.2) hT
    refine measure_mono_null (t := {x : ℝ × (ℝ × ℝ) | 0 < x.2.1 ∧
        x ∈ {p : UnforcedLeray.B0220.Profile | ¬ (p ∈ UnforcedLeray.B0220.cell c → u p = v p)}} ∪
        {x : ℝ × (ℝ × ℝ) | ¬ (0 < x.2.1) ∧
        (x.1, (x.2.1 + c, x.2.2)) ∈
          {p : UnforcedLeray.B0220.Profile | ¬ (p ∈ UnforcedLeray.B0220.cell c → u p = v p)}})
      ?_ (measure_union_null hS1 hS2)
    intro x hx
    obtain ⟨hG, hne⟩ := not_imp.1 hx
    have hs : 0 < x.1 := hG.1
    have hq : x.2.1 ∈ Ico (-c / 2) (c / 2) := by
      have := hG.2
      unfold qCell at this
      exact this.1
    have hcellx := cellPtInv_mem_cell hc hs hq
    have hZx := not_imp.2 (⟨hcellx, hne⟩ : _ ∧ _)
    by_cases h0 : 0 < x.2.1
    · have hcp : UnforcedLeray.Short.PartIIIb.NearInst.Masked.cellPtInv c x = x := by
        unfold UnforcedLeray.Short.PartIIIb.NearInst.Masked.cellPtInv
        rw [if_pos h0]
      rw [hcp] at hZx
      exact Or.inl ⟨h0, hZx⟩
    · have hcp : UnforcedLeray.Short.PartIIIb.NearInst.Masked.cellPtInv c x =
          (x.1, (x.2.1 + c, x.2.2)) := by
        unfold UnforcedLeray.Short.PartIIIb.NearInst.Masked.cellPtInv
        rw [if_neg h0]
      rw [hcp] at hZx
      exact Or.inr ⟨h0, hZx⟩
  have hac := ageμ_ac_volume' c (-3 / 2)
  filter_upwards [ae_ageμ_mem hc (-3 / 2), hac.ae_le hgood] with x hxG hxeq
  unfold velF
  rw [hxeq hxG]

end UnforcedLeray.Short.PartIIa.N01
