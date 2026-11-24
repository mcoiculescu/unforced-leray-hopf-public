import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.CellPtShared

/-!
# `cellPtHT_eq`: the recentring carries `H_T` to `c · ageμ c (-1/2)` (source 1641-1643, 2676-2679)

Proves `cellPtHT_eq : CellPtHT c`, i.e. `map (cellPt c) (measureHT c) = c • ageμ c (-1/2)`.

Route (shared, `CellPtShared.lean`). The cell measure is the product `ds ⊗ (dq|_{(0,c]}) ⊗ dη`, and `cellPt` is the product map
`id × (ctT c × id)`, where `ctT c q = q` for `q < c/2` and `ctT c q = q - c` otherwise.  Push-forward
commutes with products (`Measure.map_prod_map`), and `ctT c` pushes `dq|_{(0,c]}` to Lebesgue measure
on `[-c/2, c/2)` (`ct_map_T`, via the `q`-integral split at `c/2`, one translation by `c`, and the
endpoint changes `Ioo ~ Ico`).  The right-hand side is the same product with the normalised cell.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Short.PartIIIb.NearInst.Delta
  UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Blueprint.Planar

/-- **`cellPtHT_eq`** (source 1641-1643, 2676-2679): the recentring `cellPt` carries the tensor
measure `s^{-1/2} ds dq dη` on the cell to `c · ageμ c (-1/2)`. -/
theorem cellPtHT_eq (c : ℝ) (hc : 0 < c) : CellPtHT c := by
  show Measure.map (cellPt c) (UnforcedLeray.Short.PartIIa.measureHT c) =
    ENNReal.ofReal c • ageμ c (-1 / 2)
  have ha : (-1 / 2 : ℝ) = -(1 / 2) := by norm_num
  rw [UnforcedLeray.Short.PartIIa.measureHT, ha]
  exact ct_map_cellPt hc

end UnforcedLeray.Short.PartIIIb.NearInst.Masked
