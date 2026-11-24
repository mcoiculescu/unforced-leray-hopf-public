import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_proj2
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Basic
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.CellPtH

/-!
# The lift of a smooth force is its complexified smooth representative (organize task
`PartIII-b:C/flatset/col/7/1/1/2/4/2/3/1`)

Source `shorter-proof-2026-11-02.tex` 1684-1689 (classical case), 2667 (recentring `cellPt`, fields
`c`-periodic in `q`). Proves `SFCLiftForce` (`Sub/PartIII-b_C_flatset_col_7_1_1_2_4_2_proj2.lean`).

Route: `NearInst.ae_cellPt_of` pulls the chart-a.e. identity `velC g = F` back along `cellPt` for
`measureH`-a.e. point (`Masked.cellPtH_eq`); `cellPt` moves `q` by a multiple of `c`, so `F` is unchanged
by periodicity in `q`; `merC` is `toMC` of the componentwise complexification.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- `cellPt` does not change `F` when `F` is `c`-periodic in `q`. -/
theorem sfcCellPt_periodic {c : ℝ} (F : Chart → Fin 2 → ℝ)
    (hFp : ∀ s q η, F (s, (q + c, η)) = F (s, (q, η)))
    (p : Chart) :
    F (UnforcedLeray.Short.PartIIIb.NearInst.cellPt c p) = F p := by
  obtain ⟨s, q, η⟩ := p
  unfold UnforcedLeray.Short.PartIIIb.NearInst.cellPt
  dsimp only
  split_ifs with h
  · rfl
  · have := hFp s (q - c) η
    rw [sub_add_cancel] at this
    exact this.symm

theorem sfcLiftForce : SFCLiftForce := by
  intro c hc g F hFp hFae f' hlift
  have hH := UnforcedLeray.Short.PartIIIb.NearInst.Masked.cellPtH_eq c hc
  have h1 := UnforcedLeray.Short.PartIIIb.NearInst.ae_cellPt_of hH hFae
  filter_upwards [hlift, h1] with p hp1 hp2
  have hF := sfcCellPt_periodic F hFp p
  have key : UnforcedLeray.Short.PartIIIb.NearInst.merC
      (g (UnforcedLeray.Short.PartIIIb.NearInst.cellPt c p)) =
      toMC fun i => ((F p i : ℝ) : ℂ) := by
    unfold UnforcedLeray.Short.PartIIIb.NearInst.merC toMC
    congr 1
    funext i
    have hi := hp2 i
    unfold UnforcedLeray.Short.PartIIIb.NearInst.velC at hi
    rw [hF] at hi
    rw [← hi]
  rw [hp1]
  exact key

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
