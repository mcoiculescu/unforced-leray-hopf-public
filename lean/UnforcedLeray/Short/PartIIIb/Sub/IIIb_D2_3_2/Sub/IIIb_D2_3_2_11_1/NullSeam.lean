import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Sub.IIIb_D2_3_2_11_1

/-!
# The gain-weighted chart measures give zero mass off `chartDom c` (`PartIII-b:IIIb-D2/3/2/11/1`, source 4284-4286, 2666-2700)

`ageμ c (-1/2)` is carried by `s > 0` and by the cell `-c/2 ≤ q < c/2`, and the seam `q = -c/2`
is null, so it gives zero mass to `(chartDom c)ᶜ = {s ≤ 0} ∪ {|q| ≥ c/2}`.  The two gain-weighted
measures are absolutely continuous with respect to it.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `ageμ c a` is carried by `s > 0`. -/
theorem ns_ae_pos (c a : ℝ) : ∀ᵐ p ∂(UnforcedLeray.Axi.ageμ c a), 0 < p.1 := by
  rw [ae_iff]
  have hset : {p : Chart | ¬ 0 < p.1} = Iic (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)) := by
    ext p; simp
  rw [hset]
  unfold UnforcedLeray.Axi.ageμ
  haveI : SFinite (UnforcedLeray.Cyl.avgμ c) := by
    unfold UnforcedLeray.Cyl.avgμ
    infer_instance
  have h0 : (volume.restrict (Ioi (0 : ℝ))).restrict (Iic (0 : ℝ)) = 0 := by
    rw [Measure.restrict_restrict measurableSet_Iic]
    have hempty : Iic (0 : ℝ) ∩ Ioi (0 : ℝ) = ∅ := by
      ext x; simp
    rw [hempty, Measure.restrict_empty]
  rw [Measure.prod_prod, withDensity_apply _ measurableSet_Iic, h0, lintegral_zero_measure,
    zero_mul]

/-- `ageμ c a` is carried by the cell in the second coordinate: `-c/2 ≤ q < c/2`. -/
theorem ns_ae_Ico (c a : ℝ) :
    ∀ᵐ p ∂(UnforcedLeray.Axi.ageμ c a), p.2.1 ∈ Ico (-c / 2) (c / 2) := by
  rw [ae_iff]
  have hset : {p : Chart | ¬ p.2.1 ∈ Ico (-c / 2) (c / 2)}
      = (univ : Set ℝ) ×ˢ ((Ico (-c / 2) (c / 2))ᶜ ×ˢ (univ : Set ℝ)) := by
    ext p; simp
  rw [hset]
  unfold UnforcedLeray.Axi.ageμ
  haveI : SFinite (UnforcedLeray.Cyl.avgμ c) := by
    unfold UnforcedLeray.Cyl.avgμ
    infer_instance
  have hcell : MeasurableSet (UnforcedLeray.Cyl.cell c) := by
    unfold UnforcedLeray.Cyl.cell
    exact measurableSet_Ico.prod MeasurableSet.univ
  have hT : UnforcedLeray.Cyl.avgμ c ((Ico (-c / 2) (c / 2))ᶜ ×ˢ (univ : Set ℝ)) = 0 := by
    unfold UnforcedLeray.Cyl.avgμ UnforcedLeray.Cyl.cellμ
    rw [Measure.smul_apply, Measure.restrict_apply' hcell]
    have hempty : (Ico (-c / 2) (c / 2))ᶜ ×ˢ (univ : Set ℝ) ∩ UnforcedLeray.Cyl.cell c = ∅ := by
      ext x; simp [UnforcedLeray.Cyl.cell]
    rw [hempty]
    simp
  rw [Measure.prod_prod, hT, mul_zero]

/-- `ageμ c a` gives zero mass to the seam `q = -c/2`. -/
theorem ns_ae_ne (c a : ℝ) : ∀ᵐ p ∂(UnforcedLeray.Axi.ageμ c a), p.2.1 ≠ -c / 2 := by
  rw [ae_iff]
  have hset : {p : Chart | ¬ p.2.1 ≠ -c / 2}
      = (univ : Set ℝ) ×ˢ (({-c / 2} : Set ℝ) ×ˢ (univ : Set ℝ)) := by
    ext p; simp
  rw [hset]
  unfold UnforcedLeray.Axi.ageμ
  haveI : SFinite (UnforcedLeray.Cyl.avgμ c) := by
    unfold UnforcedLeray.Cyl.avgμ
    infer_instance
  have hcell : MeasurableSet (UnforcedLeray.Cyl.cell c) := by
    unfold UnforcedLeray.Cyl.cell
    exact measurableSet_Ico.prod MeasurableSet.univ
  have hv : (volume : Measure (ℝ × ℝ)) (({-c / 2} : Set ℝ) ×ˢ (univ : Set ℝ)) = 0 := by
    rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, zero_mul]
  have hT : UnforcedLeray.Cyl.avgμ c (({-c / 2} : Set ℝ) ×ˢ (univ : Set ℝ)) = 0 := by
    unfold UnforcedLeray.Cyl.avgμ UnforcedLeray.Cyl.cellμ
    rw [Measure.smul_apply, Measure.restrict_apply' hcell]
    have hinter : (volume : Measure (ℝ × ℝ))
        ((({-c / 2} : Set ℝ) ×ˢ (univ : Set ℝ)) ∩ UnforcedLeray.Cyl.cell c) = 0 :=
      measure_mono_null Set.inter_subset_left hv
    rw [hinter]
    simp
  rw [Measure.prod_prod, hT, mul_zero]

/-- `ageμ c (-1/2)` is carried by `chartDom c`, almost everywhere. -/
theorem ns_ae_chart (c : ℝ) : ∀ᵐ p ∂(UnforcedLeray.Axi.ageμ c (-1 / 2)), p ∈ chartDom c := by
  filter_upwards [ns_ae_pos c (-1 / 2), ns_ae_Ico c (-1 / 2), ns_ae_ne c (-1 / 2)]
    with p h1 h2 h3
  show 0 < p.1 ∧ |p.2.1| < c / 2
  refine ⟨h1, ?_⟩
  rw [abs_lt]
  exact ⟨lt_of_le_of_ne (by linarith [h2.1]) (fun h => h3 (by rw [← h]; ring)),
    by linarith [h2.2]⟩

/-- `ageμ c (-1/2)` gives zero mass to `(chartDom c)ᶜ`. -/
theorem ns_ageμ_null (c : ℝ) : UnforcedLeray.Axi.ageμ c (-1 / 2) (chartDom c)ᶜ = 0 :=
  ae_iff.mp (ns_ae_chart c)

theorem gainMeasures_null_off_chartDom (c mZ ρb γ ν : ℝ) (hc : 0 < c) :
    gainZ1Measure c mZ γ ν (chartDom c)ᶜ = 0 ∧ gainHTMeasure c ρb γ ν (chartDom c)ᶜ = 0 := by
  have hA := ns_ageμ_null c
  have hZ1 : z1Measure c mZ (chartDom c)ᶜ = 0 := by
    unfold z1Measure
    exact withDensity_absolutelyContinuous _ _ hA
  have hG1 : gainZ1Measure c mZ γ ν (chartDom c)ᶜ = 0 := by
    unfold gainZ1Measure
    exact withDensity_absolutelyContinuous _ _ hZ1
  have hHT : htRhoMeasure c ρb (chartDom c)ᶜ = 0 := by
    unfold htRhoMeasure
    rw [Measure.smul_apply, hA, smul_zero]
  have hG2 : gainHTMeasure c ρb γ ν (chartDom c)ᶜ = 0 := by
    unfold gainHTMeasure
    exact withDensity_absolutelyContinuous _ _ hHT
  exact ⟨hG1, hG2⟩

end UnforcedLeray.Short.PartIIIb.Concrete
