import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_4_1_of

/-!
# `AgeμOpenPos`: `ageμ c a` charges every nonempty open subset of the strip

Drafting task `PartIII-b:C/flatset/col/7/1/1/2/4/2/4/1/3` (source
`the November 2 reference manuscript` lines 1650-1656, 1684-1689, 3426-3430).

`ageμ c a = (volume.restrict (Ioi 0)).withDensity (ofReal ∘ (· ^ a)) ⊗ Cyl.avgμ c`
(`Lib/AxisymmetricB/Lift.lean:47`). A nonempty open set `U` inside `Ioi 0 × Ioo (-c/2) (c/2) × univ`
contains a box `I × B` with `I = Ioo (s0-δ) (s0+δ)` (`δ ≤ s0`, so `I ⊆ Ioi 0`) and
`B = Ioo (q0-δ) (q0+δ) × Ioo (η0-δ) (η0+δ)`. The box lies in the cell, so
`ageμ c a (I × B) = w I * avgμ c B` with both factors positive.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem ageμOpenPos : AgeμOpenPos := by
  unfold AgeμOpenPos
  intro c a hc U hU hsub hne
  obtain ⟨⟨s0, q0, η0⟩, hz⟩ := hne
  have hs0 : 0 < s0 := (hsub hz).1
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU _ hz
  set δ : ℝ := min ε s0 with hδdef
  have hδpos : 0 < δ := lt_min hε hs0
  have hδε : δ ≤ ε := min_le_left _ _
  have hδs : δ ≤ s0 := min_le_right _ _
  -- the box lies in `U`
  have hbox : ∀ s ∈ Ioo (s0 - δ) (s0 + δ), ∀ q ∈ Ioo (q0 - δ) (q0 + δ),
      ∀ η ∈ Ioo (η0 - δ) (η0 + δ), (s, (q, η)) ∈ U := by
    intro s hs q hq η hη
    apply hball
    obtain ⟨hs1, hs2⟩ := hs
    obtain ⟨hq1, hq2⟩ := hq
    obtain ⟨hη1, hη2⟩ := hη
    rw [Metric.mem_ball, Prod.dist_eq, Prod.dist_eq, Real.dist_eq, Real.dist_eq, Real.dist_eq]
    simp only [max_lt_iff, abs_sub_lt_iff]
    refine ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  -- the box lies in the cell
  have hBcell : Ioo (q0 - δ) (q0 + δ) ×ˢ Ioo (η0 - δ) (η0 + δ) ⊆ UnforcedLeray.Cyl.cell c := by
    intro x hx
    obtain ⟨q, η⟩ := x
    obtain ⟨hq, hη⟩ := hx
    have hpt := hsub (hbox s0 ⟨by linarith, by linarith⟩ q hq η hη)
    have hq' : q ∈ Ioo (-(c / 2)) (c / 2) := ⟨hpt.2.1.1, hpt.2.1.2⟩
    exact ⟨⟨by linarith [hq'.1], by linarith [hq'.2]⟩, trivial⟩
  -- the box is contained in `U`
  have hsubBox : Ioo (s0 - δ) (s0 + δ) ×ˢ (Ioo (q0 - δ) (q0 + δ) ×ˢ Ioo (η0 - δ) (η0 + δ)) ⊆ U := by
    intro x hx
    obtain ⟨s, q, η⟩ := x
    exact hbox s hx.1 q hx.2.1 η hx.2.2
  have hI : Ioo (s0 - δ) (s0 + δ) ⊆ Ioi (0 : ℝ) := by
    intro x hx
    show 0 < x
    linarith [hx.1]
  -- positivity of the `s`-factor
  have hwI : 0 < (volume.restrict (Ioi (0 : ℝ))).withDensity
      (fun s : ℝ => ENNReal.ofReal (s ^ a)) (Ioo (s0 - δ) (s0 + δ)) := by
    rw [withDensity_apply _ measurableSet_Ioo, Measure.restrict_restrict measurableSet_Ioo,
      Set.inter_eq_left.2 hI, setLIntegral_pos_iff (measurable_ofReal_rpow a)]
    have h1 : 0 < volume (Ioo (s0 - δ) (s0 + δ)) := by
      rw [Real.volume_Ioo]
      exact ENNReal.ofReal_pos.2 (by linarith)
    have hsub2 : Ioo (s0 - δ) (s0 + δ) ⊆
        Function.support (fun s : ℝ => ENNReal.ofReal (s ^ a)) ∩ Ioo (s0 - δ) (s0 + δ) := by
      intro x hx
      refine ⟨?_, hx⟩
      have hxpos : 0 < x := hI hx
      exact (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos hxpos a)).ne'
    exact lt_of_lt_of_le h1 (measure_mono hsub2)
  -- positivity of the cell factor
  have hBpos : 0 < UnforcedLeray.Cyl.avgμ c
      (Ioo (q0 - δ) (q0 + δ) ×ˢ Ioo (η0 - δ) (η0 + δ)) := by
    rw [UnforcedLeray.Cyl.avgμ, Measure.smul_apply, UnforcedLeray.Cyl.cellμ,
      Measure.restrict_apply (measurableSet_Ioo.prod measurableSet_Ioo),
      Set.inter_eq_left.2 hBcell, smul_eq_mul, Measure.volume_eq_prod, Measure.prod_prod,
      Real.volume_Ioo, Real.volume_Ioo]
    refine ENNReal.mul_pos (ENNReal.ofReal_pos.2 (inv_pos.2 hc)).ne' ?_
    refine (ENNReal.mul_pos ?_ ?_).ne'
    · exact (ENNReal.ofReal_pos.2 (by linarith)).ne'
    · exact (ENNReal.ofReal_pos.2 (by linarith)).ne'
  have : SFinite (UnforcedLeray.Cyl.avgμ c) := by
    unfold UnforcedLeray.Cyl.avgμ
    infer_instance
  -- conclude
  have hprod : UnforcedLeray.Axi.ageμ c a
      (Ioo (s0 - δ) (s0 + δ) ×ˢ (Ioo (q0 - δ) (q0 + δ) ×ˢ Ioo (η0 - δ) (η0 + δ))) =
      (volume.restrict (Ioi (0 : ℝ))).withDensity (fun s : ℝ => ENNReal.ofReal (s ^ a))
        (Ioo (s0 - δ) (s0 + δ)) *
      UnforcedLeray.Cyl.avgμ c (Ioo (q0 - δ) (q0 + δ) ×ˢ Ioo (η0 - δ) (η0 + δ)) := by
    rw [UnforcedLeray.Axi.ageμ, Measure.prod_prod]
  calc (0 : ℝ≥0∞) < _ := ENNReal.mul_pos hwI.ne' hBpos.ne'
    _ = _ := hprod.symm
    _ ≤ UnforcedLeray.Axi.ageμ c a U := measure_mono hsubBox

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
