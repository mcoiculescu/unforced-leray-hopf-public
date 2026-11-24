import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.HkStep.Shared

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace UnforcedLeray.Short.IIIa

/-- On a compact set the weighted cell measure is dominated by a multiple of Lebesgue measure. -/
theorem cellMeasure_restrict_le {c m : ℝ} {S : Set (ℝ × ℝ)} (hS : IsCompact S) :
    ∃ C : ℝ≥0, 0 < C ∧ (B0579.cellMeasure c m).restrict S ≤ (C : ℝ≥0∞) • (volume : Measure (ℝ × ℝ)) := by
  obtain ⟨M, hM⟩ := hS.exists_bound_of_continuousOn
    ((B0579.continuous_jb_rpow m).continuousOn)
  refine ⟨M.toNNReal + 1, by positivity, ?_⟩
  rw [Measure.le_iff]
  intro A hA
  rw [Measure.restrict_apply hA, B0579.cellMeasure,
    withDensity_apply _ (hA.inter hS.measurableSet), Measure.restrict_restrict (hA.inter hS.measurableSet)]
  simp only [Measure.smul_apply, smul_eq_mul]
  calc ∫⁻ x in (A ∩ S) ∩ B0579.cell c, ((B0579.density m x : ℝ≥0) : ℝ≥0∞) ∂volume
      ≤ ∫⁻ x in (A ∩ S) ∩ B0579.cell c, ((M.toNNReal + 1 : ℝ≥0) : ℝ≥0∞) ∂volume := by
        refine setLIntegral_mono' ((hA.inter hS.measurableSet).inter (B0579.measurableSet_cell c))
          fun x hx => ?_
        have h1 := hM x hx.1.2
        have h2 : (B0579.density m x : ℝ) ≤ ((M.toNNReal + 1 : ℝ≥0) : ℝ) := by
          rw [B0579.coe_density]
          have := le_trans (le_abs_self _) (by simpa [Real.norm_eq_abs] using h1)
          have h3 : M ≤ (M.toNNReal : ℝ) := Real.le_coe_toNNReal M
          push_cast
          linarith
        exact ENNReal.coe_le_coe.2 (by exact_mod_cast h2)
    _ ≤ _ := by
        rw [setLIntegral_const]
        exact mul_le_mul_right
          (measure_mono (inter_subset_left.trans inter_subset_left)) _
