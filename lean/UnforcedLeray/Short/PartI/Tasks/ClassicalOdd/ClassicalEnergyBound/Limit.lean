import UnforcedLeray.Short.PartI.Sub.T02_3_10

/-!
# Part I, task `PartI:ClassicalOdd/ClassicalEnergyBound/Limit`: the limit leaf `EbLimit`

Source of record: `the November 2 reference manuscript`, lines 276-282
(the transverse cutoff `φ_R = etaCutoff R` is sent to the limit `R → ∞`).

Target: `ebLimit : EtaCutoffFacts → EbLimit`, where `EbLimit` is defined in `Sub/T02_3_10.lean`.

Strategy. For `R ≥ 1`, `EtaCutoffFacts` gives `0 ≤ φ_R ≤ 1`, and `φ_R = 1` on `|η| ≤ R`, so
`φ_R(η) → 1` pointwise as `R → ∞`. For `f ≥ 0` integrable on the cell, the integrand
`φ_R f` is dominated by `f`, so dominated convergence gives `∫_cell φ_R f → ∫_cell f`.
Each `∫_cell φ_R f` is `≤ A` for `R ≥ 1` by hypothesis, so the limit is `≤ A`.
-/

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartI

/-- **Leaf `EbLimit`** (`PartI:ClassicalOdd/ClassicalEnergyBound/Limit`): from the cutoff facts,
if `∫_cell φ_R f ≤ A` for all `R ≥ 1` and `f ≥ 0` is integrable on the cell, then
`∫_cell f ≤ A`. -/
theorem ebLimit : EtaCutoffFacts → EbLimit := by
  intro hF
  unfold EtaCutoffFacts at hF
  obtain ⟨_C₀, _hC₀, hcut⟩ := hF
  unfold EbLimit
  intro c _hc f A hf0 hfint hA
  have hfint' : Integrable f (volume.restrict (Cyl.cell c)) := hfint
  -- Facts about the cutoff for `R ≥ 1`.
  have hcont : ∀ R : ℝ, 1 ≤ R → Continuous (etaCutoff R) := fun R hR =>
    (hcut R hR).1.continuous
  have h01 : ∀ R : ℝ, 1 ≤ R → ∀ η : ℝ, 0 ≤ etaCutoff R η ∧ etaCutoff R η ≤ 1 :=
    fun R hR η => (hcut R hR).2.1 η
  have h1 : ∀ R : ℝ, 1 ≤ R → ∀ η : ℝ, |η| ≤ R → etaCutoff R η = 1 :=
    fun R hR η hη => (hcut R hR).2.2.1 η hη
  -- Pointwise limit of the cutoff: it equals `1` once `R ≥ max 1 |η|`.
  have hlim1 : ∀ η : ℝ, Tendsto (fun R : ℝ => etaCutoff R η) atTop (𝓝 1) := by
    intro η
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (max 1 |η|)] with R hR
    have hR1 : (1 : ℝ) ≤ R := le_trans (le_max_left _ _) hR
    have hRa : |η| ≤ R := le_trans (le_max_right _ _) hR
    exact (h1 R hR1 η hRa).symm
  -- Pointwise convergence of the integrand on the cell.
  have hpt : ∀ᵐ z ∂(volume.restrict (Cyl.cell c)),
      Tendsto (fun R : ℝ => etaCutoff R z.2 * f z) atTop (𝓝 (f z)) := by
    refine ae_of_all _ fun z => ?_
    have h := (hlim1 z.2).mul_const (f z)
    rwa [one_mul] at h
  -- Domination by `f` for `R ≥ 1`.
  have hdom : ∀ᶠ R in atTop, ∀ᵐ z ∂(volume.restrict (Cyl.cell c)),
      ‖etaCutoff R z.2 * f z‖ ≤ f z := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
    refine ae_of_all _ fun z => ?_
    rw [Real.norm_of_nonneg (mul_nonneg (h01 R hR z.2).1 (hf0 z))]
    exact mul_le_of_le_one_left (hf0 z) (h01 R hR z.2).2
  -- Measurability of the integrands for `R ≥ 1`.
  have hmeas : ∀ᶠ R in atTop,
      AEStronglyMeasurable (fun z : Cyl.Plane => etaCutoff R z.2 * f z)
        (volume.restrict (Cyl.cell c)) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
    have hc2 : Continuous (fun z : Cyl.Plane => etaCutoff R z.2) :=
      (hcont R hR).comp continuous_snd
    exact hc2.aestronglyMeasurable.mul hfint'.aestronglyMeasurable
  -- Dominated convergence: the cell integrals converge to `∫_cell f`.
  have hint : Tendsto (fun R : ℝ => ∫ z in Cyl.cell c, etaCutoff R z.2 * f z) atTop
      (𝓝 (∫ z in Cyl.cell c, f z)) :=
    tendsto_integral_filter_of_dominated_convergence f hmeas hdom hfint' hpt
  -- The hypothesis bounds the cell integrals by `A` for `R ≥ 1`, so the limit is at most `A`.
  exact le_of_tendsto hint ((eventually_ge_atTop (1 : ℝ)).mono fun R hR => hA R hR)

end UnforcedLeray.Short.PartI
