import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1_org2_bridge
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1_org2_bridge.CellMap

/-!
# `BridgeTransfer`: a.e. identity from `(Profile, measureH)` to `(Chart, ageμ c (-3/2))`

Source `the November 2 reference manuscript` 1650-1656, 1684-1689.
`cellPt` is the recentring of the cell, and `ageμ c (-3/2)` lives on the cell, so no periodicity
hypothesis is needed: `CellMap.ae_ageμ_of_ae_cellPt` gives the null-set transfer, using
`measureH c (cellPt⁻¹' A) = c * ageμ c (-3/2) A` for measurable `A`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem bridgeTransfer : BridgeTransfer := by
  intro c hc b F h
  rw [show (-3 / 2 : ℝ) = -(3 / 2) by norm_num]
  refine CellMap.ae_ageμ_of_ae_cellPt hc (P := fun x => NearInst.velC b x = F x) ?_
  filter_upwards [h] with p hp
  show NearInst.velC b (NearInst.cellPt c p) = F (NearInst.cellPt c p)
  funext i
  exact congrArg (fun v : UnforcedLeray.B0223.MeridC => v i) hp

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
