import UnforcedLeray.Short.PartIIb.Sub.T11_6
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.CellStream.HrBox

/-!
# Part II-b, leaf `PartII-b:T11/6/6` (`CutLocInt`): local integrability of the cut-off components

Source of record: `the November 2 reference manuscript`, SP 1900-1903 (the space
`H_r` with density `s^{r/2-5/2}`). The statement is `CutLocInt` of `Sub/T11_6.lean`, unchanged.

Proof. A compact `k` lies in a cube `[-T, T] × [-T, T] × [-T, T]` (`cli6_cube`). On the box
`Box := [δ, T] × [-T, T] × [-T, T]` the function `b · i` is integrable by `hrBoxIntegrable`
(with `σ := δ`), so its indicator on `{δ < s}` is integrable on `Box` (`IntegrableOn.indicator`).
On the rest of the cube `B` the indicator vanishes, so it is integrable on `B`
(`IntegrableOn.of_forall_sdiff_eq_zero`), hence on `k ⊆ B`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- A compact subset of `Coord` lies in a cube `[-T, T] × [-T, T] × [-T, T]`. -/
theorem cli6_cube (k : Set Coord) (hk : IsCompact k) :
    ∃ T : ℝ, k ⊆ Icc (-T) T ×ˢ (Icc (-T) T ×ˢ Icc (-T) T) := by
  obtain ⟨T, hT⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Coord)).1 hk.isBounded
  refine ⟨T, fun x hx => ?_⟩
  have hx' : ‖x‖ ≤ T := mem_closedBall_zero_iff.1 (hT hx)
  have h1 : ‖x.1‖ ≤ T := (norm_fst_le x).trans hx'
  have h2 : ‖x.2.1‖ ≤ T := ((norm_fst_le x.2).trans (norm_snd_le x)).trans hx'
  have h3 : ‖x.2.2‖ ≤ T := ((norm_snd_le x.2).trans (norm_snd_le x)).trans hx'
  rw [Real.norm_eq_abs, abs_le] at h1 h2 h3
  exact ⟨⟨h1.1, h1.2⟩, ⟨h2.1, h2.2⟩, ⟨h3.1, h3.2⟩⟩

/-- **Leaf `PartII-b:T11/6/6`** (`CutLocInt`, the cut-off components are locally integrable). -/
theorem cutLocInt : CutLocInt := by
  unfold CutLocInt
  intro c r δ b hc hr hδ hb i
  rw [MeasureTheory.locallyIntegrable_iff]
  intro k hk
  unfold cutC
  obtain ⟨T, hT⟩ := cli6_cube k hk
  have hg : IntegrableOn (fun x : Coord => b x i)
      (Icc δ T ×ˢ (Icc (-T) T ×ˢ Icc (-T) T)) volume :=
    hrBoxIntegrable c r b hc hr hb δ T T T hδ i
  have hSm : MeasurableSet {x : Coord | δ < x.1} :=
    (isOpen_lt continuous_const continuous_fst).measurableSet
  have hf : IntegrableOn (indicator {x : Coord | δ < x.1} (fun x : Coord => b x i))
      (Icc δ T ×ˢ (Icc (-T) T ×ˢ Icc (-T) T)) volume :=
    hg.indicator hSm
  have hBm : MeasurableSet (Icc (-T) T ×ˢ (Icc (-T) T ×ˢ Icc (-T) T) : Set Coord) :=
    measurableSet_Icc.prod (measurableSet_Icc.prod measurableSet_Icc)
  have hzero : ∀ x ∈ (Icc (-T) T ×ˢ (Icc (-T) T ×ˢ Icc (-T) T) : Set Coord) \
      (Icc δ T ×ˢ (Icc (-T) T ×ˢ Icc (-T) T)),
      indicator {x : Coord | δ < x.1} (fun x : Coord => b x i) x = 0 := by
    intro x hx
    apply indicator_of_notMem
    intro hxS
    have hxS' : δ < x.1 := hxS
    apply hx.2
    exact ⟨⟨hxS'.le, hx.1.1.2⟩, hx.1.2⟩
  have hB : IntegrableOn (indicator {x : Coord | δ < x.1} (fun x : Coord => b x i))
      (Icc (-T) T ×ˢ (Icc (-T) T ×ˢ Icc (-T) T)) volume :=
    hf.of_forall_sdiff_eq_zero hBm hzero
  exact hB.mono_set hT

end UnforcedLeray.Short.IIb
