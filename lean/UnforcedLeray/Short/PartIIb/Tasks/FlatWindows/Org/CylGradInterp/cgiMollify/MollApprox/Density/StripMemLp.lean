import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T13_1_5_5_7_1

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology

theorem cylMeas_eq_strip_smul (c : ℝ) (hc : 0 < c) :
    cylMeas c = ENNReal.ofReal c⁻¹ • (volume : Measure Coord).restrict (moStrip c) := by
  unfold cylMeas UnforcedLeray.Cyl.avgμ UnforcedLeray.Cyl.cellμ moStrip
  rw [Measure.prod_smul_right]
  congr 1
  have h1 : (volume : Measure ℝ).prod ((volume : Measure (ℝ × ℝ)).restrict (UnforcedLeray.Cyl.cell c))
      = ((volume : Measure ℝ).restrict univ).prod ((volume : Measure (ℝ × ℝ)).restrict (UnforcedLeray.Cyl.cell c)) := by
    rw [Measure.restrict_univ]
  rw [h1, Measure.prod_restrict]
  rfl

theorem mollStripMemLp_proof : MollStripMemLp := by
  intro c r hc hr f hf hfin
  have hk : ENNReal.ofReal c⁻¹ ≠ 0 := (ENNReal.ofReal_pos.mpr (inv_pos.mpr hc)).ne'
  have hstrip : MeasurableSet (moStrip c) :=
    MeasurableSet.univ.prod (measurableSet_Ico.prod MeasurableSet.univ)
  refine ⟨hf.indicator hstrip, ?_⟩
  rw [cylMeas_eq_strip_smul c hc, eLpNorm_smul_measure_of_ne_zero hk] at hfin
  rw [eLpNorm_indicator_eq_eLpNorm_restrict hstrip]
  have hne : (ENNReal.ofReal c⁻¹) ^ (1 / ENNReal.ofReal r).toReal ≠ 0 :=
    (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr (inv_pos.mpr hc)) ENNReal.ofReal_ne_top).ne'
  rw [smul_eq_mul] at hfin
  refine lt_top_iff_ne_top.mpr fun htop => ?_
  rw [htop, ENNReal.mul_top hne] at hfin
  exact lt_irrefl _ hfin

end UnforcedLeray.Short.IIb

end
