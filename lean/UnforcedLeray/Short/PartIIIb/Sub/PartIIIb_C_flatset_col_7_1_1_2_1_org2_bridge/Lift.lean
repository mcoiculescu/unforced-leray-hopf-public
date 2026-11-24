import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1_org2_bridge
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1_org2_bridge.CellMap
import UnforcedLeray.Short.PartIIIb.NearInst.Body.Defs

/-!
# `BridgeLift`: an `H`-representative of the recentred smooth force

Source `the November 2 reference manuscript` 1650-1656, 1684-1689.
`cellPt` pushes `measureH c` to `c • ageμ c (-3/2)` (`CellMap.map_cellPt_measureH`), so
`g ∘ cellPt` is `L²(measureH c)` whenever `g ∈ L²(ageμ c (-3/2))`; `merCL` is continuous linear,
so the composite is an `H`-element.  Smoothness of `g` is not needed.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem bridgeLift : BridgeLift := by
  intro c hc g _hg
  have hcp := CellMap.measurable_cellPt' c
  have hg2 : MemLp (⇑g) 2 (ageμ c (-(3 / 2))) := by
    rw [show (-(3 / 2) : ℝ) = -3 / 2 by norm_num]
    exact Lp.memLp g
  have h1 : MemLp (⇑g) 2 ((UnforcedLeray.B0220.measureH c).map (NearInst.cellPt c)) := by
    rw [CellMap.map_cellPt_measureH hc]
    exact hg2.smul_measure ENNReal.ofReal_ne_top
  have h2 : MemLp (⇑g ∘ NearInst.cellPt c) 2 (UnforcedLeray.B0220.measureH c) :=
    (memLp_map_measure_iff h1.aestronglyMeasurable hcp.aemeasurable).1 h1
  have h3 : MemLp (fun p => NearInst.merC (g (NearInst.cellPt c p))) 2
      (UnforcedLeray.B0220.measureH c) :=
    h2.continuousLinearMap_comp NearInst.Body.merCL
  exact ⟨h3.toLp _, h3.coeFn_toLp⟩

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
