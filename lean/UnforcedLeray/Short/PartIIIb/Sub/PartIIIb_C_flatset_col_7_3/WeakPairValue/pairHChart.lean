import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_3_6
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1_org2_bridge.CellMap
import UnforcedLeray.Short.PartIIb.Tasks.HilbertEnergy.SPeriodic

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate InnerProductSpace

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.B0220 (HSpace measureH Profile)
open UnforcedLeray.B0223 (MeridC)

/-- The recentred cell `Ico (-c/2) (c/2)` of `Axi.qCell` is `B0579.cell`. -/
theorem qCell_eq_B0579_cell (c : ℝ) : Axi.qCell c = B0579.cell c := by
  unfold Axi.qCell B0579.cell
  rw [neg_div]

/-- The pushforward of `measureH c` under `cellPt` is the chart density `s^{-3/2}` on the chart
cell `Ioi 0 ×ˢ B0579.cell c`. -/
theorem map_cellPt_measureH_chart {c : ℝ} (hc : 0 < c) :
    (measureH c).map (NearInst.cellPt c) =
      (volume.restrict (Ioi (0 : ℝ) ×ˢ B0579.cell c)).withDensity
        (fun x : Chart => ENNReal.ofReal (x.1 ^ (-(3 / 2 : ℝ)))) := by
  have hSm : MeasurableSet (Ioi (0 : ℝ) ×ˢ B0579.cell c) :=
    measurableSet_Ioi.prod (B0579.measurableSet_cell c)
  rw [CellMap.map_cellPt_measureH hc, UnforcedLeray.Short.IIb.ageμ_eq_withDensity hc (-(3 / 2)),
    ← withDensity_smul' _ _ ENNReal.ofReal_ne_top, ← withDensity_indicator hSm]
  congr 1
  funext x
  by_cases hx : x ∈ Ioi (0 : ℝ) ×ˢ B0579.cell c
  · have hx' : x ∈ Ioi (0 : ℝ) ×ˢ Axi.qCell c := by
      rw [qCell_eq_B0579_cell]; exact hx
    simp only [UnforcedLeray.Short.IIb.dens, Pi.smul_apply, smul_eq_mul,
      Set.indicator_of_mem hx, Set.indicator_of_mem hx', Pi.one_apply, mul_one]
    rw [← ENNReal.ofReal_mul hc.le, ← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]
  · have hx' : x ∉ Ioi (0 : ℝ) ×ˢ Axi.qCell c := by
      rw [qCell_eq_B0579_cell]; exact hx
    simp [UnforcedLeray.Short.IIb.dens, Set.indicator_of_notMem hx,
      Set.indicator_of_notMem hx']

theorem pairHChart : PairHChart := by
  intro c hc g h' hh' w hw hint
  have hSm : MeasurableSet (Ioi (0 : ℝ) ×ˢ B0579.cell c) :=
    measurableSet_Ioi.prod (B0579.measurableSet_cell c)
  have hcp : Measurable (NearInst.cellPt c) := CellMap.measurable_cellPt' c
  have hρE : Measurable (fun x : Chart => ENNReal.ofReal (x.1 ^ (-(3 / 2 : ℝ)))) := by
    fun_prop
  have hρm : Measurable (fun x : Chart => (x.1 ^ (-(3 / 2 : ℝ))).toNNReal) := by
    fun_prop
  -- `F` is almost everywhere measurable for the pushforward (from integrability of the RHS)
  have hF_aesm : AEStronglyMeasurable (fun x : Chart => inner ℂ (w x) (NearInst.merC (g x)))
      ((volume.restrict (Ioi (0 : ℝ) ×ˢ B0579.cell c)).withDensity
        (fun x : Chart => ENNReal.ofReal (x.1 ^ (-(3 / 2 : ℝ))))) := by
    refine (aestronglyMeasurable_withDensity_iff (f := fun x : Chart => (x.1 ^ (-(3 / 2 : ℝ))).toNNReal)
      hρm).2 ?_
    refine hint.aestronglyMeasurable.congr ?_
    filter_upwards [ae_restrict_mem hSm] with x hx
    have hx0 : 0 < x.1 := hx.1
    rw [Real.coe_toNNReal _ (Real.rpow_nonneg hx0.le _)]
  -- Step 1: the a.e. replacement of `h'` by the recentred `g`
  have step1 : pairH c (h' : Profile → MeridC) w =
      ∫ p, inner ℂ (w (NearInst.cellPt c p)) (NearInst.merC (g (NearInst.cellPt c p)))
        ∂(measureH c) := by
    unfold pairH
    refine integral_congr_ae ?_
    filter_upwards [hh'] with p hp
    rw [hp, hw p]
  -- Step 2: change of variables along `cellPt`
  have step2 : ∫ p, inner ℂ (w (NearInst.cellPt c p)) (NearInst.merC (g (NearInst.cellPt c p)))
        ∂(measureH c) =
      ∫ x, inner ℂ (w x) (NearInst.merC (g x)) ∂((measureH c).map (NearInst.cellPt c)) := by
    refine (integral_map (f := fun x : Chart => inner ℂ (w x) (NearInst.merC (g x)))
      hcp.aemeasurable ?_).symm
    rw [map_cellPt_measureH_chart hc]
    exact hF_aesm
  -- Step 3: the density gives the chart-cell integral
  rw [step1, step2, map_cellPt_measureH_chart hc,
    integral_withDensity_eq_integral_toReal_smul hρE
      (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_mem hSm] with x hx
  have hx0 : 0 < x.1 := hx.1
  rw [ENNReal.toReal_ofReal (Real.rpow_nonneg hx0.le _)]

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
