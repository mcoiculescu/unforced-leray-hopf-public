import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_4_2_1.FlatLerayDefs
import UnforcedLeray.Short.PartIIIb.NearInst.Body.Defs
import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.CompactWindow.Comparison.FlatStress.CellPtChangeAll

/-!


Source of record `the November 2 reference manuscript` lines 1641-1646 (`H` on the
cell `(0, c]`) and 1684-1689. The smooth representative `F` is `c`-periodic in `q`; the lift `f'` is
`measureH c`-a.e. `merC (g (cellPt c p))`; `cellPt` recentres the cell and the pullback
`cpc_map_cellPt` maps `measureH c` to `c • ageμ c (-3/2)`, on which `g = F` a.e.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.FlatLeray

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.Short.PartIIa

/-- A `c`-periodic `F` is unchanged by the recentring `cellPt`. -/
theorem liftAe_F_cellPt {c : ℝ} (F : Chart → Fin 2 → ℝ)
    (hper : ∀ s q η, F (s, (q + c, η)) = F (s, (q, η))) (p : Profile) :
    F (NearInst.cellPt c p) = F p := by
  unfold NearInst.cellPt
  split_ifs with h
  · rfl
  · have := hper p.1 (p.2.1 - c) p.2.2
    rw [sub_add_cancel] at this
    exact this.symm

/-- **Task target: the lift is a.e. the complexified smooth field** (source 1641-1646, 1684-1689). -/
theorem liftAe : LiftAe := by
  intro c hc g f' F hper hae hl
  have hae' : ∀ᵐ p ∂(UnforcedLeray.Axi.ageμ c (-3 / 2)), ∀ i, g p i = F p i := by
    filter_upwards [hae] with p hp i
    have h := hp i
    simp only [NearInst.velC] at h
    exact Complex.ofReal_inj.mp h
  have hmap : Measure.map (NearInst.cellPt c) (measureH c)
      = ENNReal.ofReal c • UnforcedLeray.Axi.ageμ c (-3 / 2) := by
    have h0 := NearInst.Masked.cpc_map_cellPt (c := c) (a := -(3 / 2)) hc
    rw [show (-3 / 2 : ℝ) = -(3 / 2) by norm_num]
    exact h0
  have hae2 : ∀ᵐ y ∂(Measure.map (NearInst.cellPt c) (measureH c)), ∀ i, g y i = F y i := by
    rw [hmap]
    exact Measure.ae_smul_measure hae' _
  have hA0 : ∀ᵐ p ∂(measureH c), ∀ i, g (NearInst.cellPt c p) i = F (NearInst.cellPt c p) i :=
    ae_of_ae_map (NearInst.Body.measurable_cellPt' c).aemeasurable hae2
  have hA : ∀ᵐ p ∂(measureH c), ∀ i, g (NearInst.cellPt c p) i = F p i := by
    filter_upwards [hA0] with p hp i
    rw [hp i, liftAe_F_cellPt (c := c) F hper p]
  unfold SFCLift at hl
  filter_upwards [hl, hA] with p h1 h2
  rw [h1]
  ext i
  simp [NearInst.merC, cplxField, h2 i]

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.FlatLeray
