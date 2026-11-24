import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1.LerayOf
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1_org2_bridge.CellMap

/-!
# Representative of a smooth force in `H` (`SmoothForceRep`)

Source `the November 2 reference manuscript` 1642-1644, 2667.
The recentring `cellPt` pushes `measureH c` to `c • ageμ c (-3/2)` (`CellMap.map_cellPt_measureH`),
so an `ageμ`-a.e. identity transfers to a `measureH c`-a.e. identity at the recentred point, and a
`c`-periodic `F` is invariant under `cellPt` (`eq_cellPt`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

theorem smoothForceRep : SmoothForceRep := by
  intro c hc g F hF hae
  -- the a.e. identity on the chart measure, as real components
  have hae' : ∀ᵐ x ∂(UnforcedLeray.Axi.ageμ c (-3 / 2)), ∀ i, g x i = F x i := by
    filter_upwards [hae] with x hx i
    have h := hx i
    simp only [NearInst.velC] at h
    exact Complex.ofReal_inj.mp h
  -- the pushforward of `measureH c` under `cellPt`, with the exponent written as `-3/2`
  have e : (-3 / 2 : ℝ) = -(3 / 2) := by norm_num
  have hm : (UnforcedLeray.B0220.measureH c).map (NearInst.cellPt c) =
      ENNReal.ofReal c • UnforcedLeray.Axi.ageμ c (-3 / 2) := by
    rw [CellMap.map_cellPt_measureH hc, e]
  have hmap : ∀ᵐ x ∂((UnforcedLeray.B0220.measureH c).map (NearInst.cellPt c)),
      ∀ i, g x i = F x i := by
    rw [hm]
    exact Measure.ae_smul_measure hae' _
  have hcell : ∀ᵐ p ∂(UnforcedLeray.B0220.measureH c),
      ∀ i, g (NearInst.cellPt c p) i = F (NearInst.cellPt c p) i :=
    ae_of_ae_map (CellMap.measurable_cellPt' c).aemeasurable hmap
  filter_upwards [hcell] with p hp
  show NearInst.merC (g (NearInst.cellPt c p)) = cvec (F p)
  rw [← eq_cellPt hF p]
  ext i
  simp only [NearInst.merC, cvec, PiLp.toLp_apply]
  rw [hp i]

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
