import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_1
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.StressPairAE

/-!
# `ChartOfNullPullback` (PartIII-b:IIIb-D2/3/1/1/1, leaf L1)

Source of record: `the November 2 reference manuscript` 2666-2668, 3256-3268.
The chart point `chartOf R c z τ` is `2c/R`-periodic in `τ`, so a chart-null set is hit only on a
null set of `(τ, z)`: the strip `(0, P]` is null by `stressPairAE_null`, and the strips
`(kP, (k+1)P]` are translates of it.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- The chart point is invariant under integer multiples of the period `2c/R` (the `key` step
of `oldPhysPeriodic`, with `k ∈ ℤ`). -/
theorem chartOf_add_int_period (R c : ℝ) (hR : 0 < R) (hc : 0 < c) (z : Space) (τ : ℝ) (k : ℤ) :
    NearInst.chartOf R c z (τ + k * (2 * c / R)) = NearInst.chartOf R c z τ := by
  have hR' : R ≠ 0 := hR.ne'
  have hc' : c ≠ 0 := hc.ne'
  unfold NearInst.chartOf
  have e1 : R * Real.log (NearInst.hRad z / R) + R * (τ + k * (2 * c / R)) / 2
      = (R * Real.log (NearInst.hRad z / R) + R * τ / 2) + k * c := by
    field_simp
    ring
  have hfl : ⌊((R * Real.log (NearInst.hRad z / R) + R * τ / 2) + k * c) / c + 1 / 2⌋
      = ⌊(R * Real.log (NearInst.hRad z / R) + R * τ / 2) / c + 1 / 2⌋ + k := by
    have h : ((R * Real.log (NearInst.hRad z / R) + R * τ / 2) + k * c) / c + 1 / 2
        = (R * Real.log (NearInst.hRad z / R) + R * τ / 2) / c + 1 / 2 + (k : ℝ) := by
      field_simp
      ring
    rw [h, Int.floor_add_intCast]
  rw [e1, hfl]
  refine Prod.ext rfl (Prod.ext ?_ rfl)
  push_cast
  ring

/-- **Chart-null sets pull back to null sets** (source 2666-2668; `stressPairAE_null`,
`chartOf_add_int_period`). -/
theorem chartOfNullPullback : ChartOfNullPullback := by
  intro R c hR hc N hN
  have hP0 : 0 < 2 * c / R := div_pos (mul_pos two_pos hc) hR
  -- the chart-null hull
  set N' : Set Chart := toMeasurable (ageμ c (-1 / 2)) N with hN'def
  have hN'm : MeasurableSet N' := measurableSet_toMeasurable _ _
  have hN'0 : ageμ c (-1 / 2) N' = 0 := by
    rw [hN'def, measure_toMeasurable]; exact hN
  have hN5 : ageμ c (-5 / 2) N' = 0 := NearInst.ageμ_absCont c (-5 / 2) (-1 / 2) hN'0
  -- the basic strip `(0, P]` is null
  have hae := NearInst.stressPairAE_null R c (2 * c / R) hR hc rfl N' hN'm hN5
  have hC : ((volume.restrict (Ioc 0 (2 * c / R))).prod (volume : Measure Space))
      {x : ℝ × Space | NearInst.chartOf R c x.2 x.1 ∈ N'} = 0 := by
    have h := ae_iff.1 hae
    simpa using h
  have hprod : (volume.restrict (Ioc 0 (2 * c / R))).prod (volume : Measure Space)
      = (volume : Measure (ℝ × Space)).restrict (Ioc 0 (2 * c / R) ×ˢ (univ : Set Space)) := by
    rw [Measure.volume_eq_prod]
    conv_lhs => rw [← Measure.restrict_univ (μ := (volume : Measure Space))]
    rw [Measure.prod_restrict]
  have hS0 : (volume : Measure (ℝ × Space))
      {x : ℝ × Space | x.1 ∈ Ioc 0 (2 * c / R) ∧ NearInst.chartOf R c x.2 x.1 ∈ N'} = 0 := by
    rw [hprod] at hC
    rw [Measure.restrict_apply' (measurableSet_Ioc.prod MeasurableSet.univ)] at hC
    have e : {x : ℝ × Space | x.1 ∈ Ioc 0 (2 * c / R) ∧ NearInst.chartOf R c x.2 x.1 ∈ N'}
        = {x : ℝ × Space | NearInst.chartOf R c x.2 x.1 ∈ N'} ∩ (Ioc 0 (2 * c / R) ×ˢ univ) := by
      ext x
      simp [and_comm]
    rw [e]
    exact hC
  -- the translated strips
  let E : ℤ → Set (ℝ × Space) := fun k =>
    {x | x.1 ∈ Ioc ((k : ℝ) * (2 * c / R)) (((k : ℝ) + 1) * (2 * c / R)) ∧
      NearInst.chartOf R c x.2 x.1 ∈ N'}
  have hstrip : ∀ k : ℤ, ∀ᵐ x ∂(volume : Measure (ℝ × Space)), x ∉ E k := by
    intro k
    have hmp : MeasurePreserving (Prod.map (fun t : ℝ => t - (k : ℝ) * (2 * c / R)) id)
        ((volume : Measure ℝ).prod (volume : Measure Space))
        ((volume : Measure ℝ).prod (volume : Measure Space)) :=
      (measurePreserving_sub_right (volume : Measure ℝ) ((k : ℝ) * (2 * c / R))).prod
        (MeasurePreserving.id (volume : Measure Space))
    have hqmp := hmp.quasiMeasurePreserving
    have hpre := hqmp.preimage_null (s := {x : ℝ × Space |
      x.1 ∈ Ioc 0 (2 * c / R) ∧ NearInst.chartOf R c x.2 x.1 ∈ N'}) hS0
    have hsub : E k ⊆ Prod.map (fun t : ℝ => t - (k : ℝ) * (2 * c / R)) id ⁻¹'
        {x : ℝ × Space | x.1 ∈ Ioc 0 (2 * c / R) ∧ NearInst.chartOf R c x.2 x.1 ∈ N'} := by
      intro x hx'
      obtain ⟨⟨h1, h2⟩, hx⟩ := hx'
      have hA : x.1 - (k : ℝ) * (2 * c / R) ∈ Ioc 0 (2 * c / R) := by
        have e : ((k : ℝ) + 1) * (2 * c / R) = (k : ℝ) * (2 * c / R) + 2 * c / R := by ring
        exact ⟨by linarith, by linarith⟩
      have hB : NearInst.chartOf R c x.2 (x.1 - (k : ℝ) * (2 * c / R))
          = NearInst.chartOf R c x.2 x.1 := by
        have h := chartOf_add_int_period R c hR hc x.2 (x.1 - (k : ℝ) * (2 * c / R)) k
        rw [sub_add_cancel] at h
        exact h.symm
      show x.1 - (k : ℝ) * (2 * c / R) ∈ Ioc 0 (2 * c / R) ∧
        NearInst.chartOf R c x.2 (x.1 - (k : ℝ) * (2 * c / R)) ∈ N'
      refine ⟨hA, ?_⟩
      rw [hB]
      exact hx
    have hE0 : (volume : Measure (ℝ × Space)) (E k) = 0 :=
      measure_mono_null hsub hpre
    exact measure_eq_zero_iff_ae_notMem.1 hE0
  have hall : ∀ᵐ x ∂(volume : Measure (ℝ × Space)), ∀ k : ℤ, x ∉ E k := ae_all_iff.2 hstrip
  filter_upwards [hall] with x hx hmem
  have hNN' : NearInst.chartOf R c x.2 x.1 ∈ N' := subset_toMeasurable _ _ hmem
  obtain ⟨k, hk1, hk2⟩ : ∃ k : ℤ, (k : ℝ) < x.1 / (2 * c / R) ∧
      x.1 / (2 * c / R) ≤ (k : ℝ) + 1 :=
    ⟨⌈x.1 / (2 * c / R)⌉ - 1, by
      push_cast
      constructor <;> linarith [Int.le_ceil (x.1 / (2 * c / R)),
        Int.ceil_lt_add_one (x.1 / (2 * c / R))]⟩
  have h1 : (k : ℝ) * (2 * c / R) < x.1 := (lt_div_iff₀ hP0).1 hk1
  have h2 : x.1 ≤ ((k : ℝ) + 1) * (2 * c / R) := (div_le_iff₀ hP0).1 hk2
  exact hx k ⟨⟨h1, h2⟩, hNN'⟩

end UnforcedLeray.Short.PartIIIb.Concrete
