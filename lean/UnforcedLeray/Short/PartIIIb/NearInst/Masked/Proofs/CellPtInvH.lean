import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.CellPtShared

/-!
# `cellPtInvH_eq`: the inverse recentring carries `ageμ c (-3/2)` to `c⁻¹ · measureH c` (source 1645, 2676-2679)

Proves `cellPtInvH_eq : CellPtInvH c`, i.e. `map (cellPtInv c) (ageμ c (-3/2)) = c⁻¹ • measureH c`.
The identity is obtained from `map cellPt (measureH c) = c • ageμ c (-3/2)` (proved here as `cellPtH_aux`)
by `cellPtInv ∘ cellPt = id` on the cell (`cellPtInv_cellPt`).

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

/-- The velocity identity `map cellPt (measureH c) = c • ageμ c (-3/2)` (source 2676-2679), proved
in this file from the same pattern as `CellPtH`. -/
theorem cellPtH_aux (c : ℝ) (hc : 0 < c) :
    Measure.map (cellPt c) (UnforcedLeray.B0220.measureH c) = ENNReal.ofReal c • ageμ c (-3 / 2) := by
  have ha : (-3 / 2 : ℝ) = -(3 / 2) := by norm_num
  rw [UnforcedLeray.B0220.measureH, ha]
  exact ct_map_cellPt hc

/-- **`cellPtInvH_eq`** (source 1645, 2676-2679): the inverse recentring carries the normalised
recentred velocity measure `ageμ c (-3/2)` to `c⁻¹ · measureH c`. -/
theorem cellPtInvH_eq (c : ℝ) (hc : 0 < c) : CellPtInvH c := by
  show Measure.map (cellPtInv c) (ageμ c (-3 / 2)) =
    ENNReal.ofReal c⁻¹ • UnforcedLeray.B0220.measureH c
  have hA : ageμ c (-3 / 2) = ENNReal.ofReal c⁻¹ •
      Measure.map (cellPt c) (UnforcedLeray.B0220.measureH c) := by
    rw [cellPtH_aux c hc, smul_smul, ← ENNReal.ofReal_mul (inv_nonneg.2 hc.le),
      inv_mul_cancel₀ hc.ne', ENNReal.ofReal_one, one_smul]
  have hae : (cellPtInv c ∘ cellPt c) =ᵐ[UnforcedLeray.B0220.measureH c] id := by
    filter_upwards [ae_mem_cell_H c] with p hp
    simp only [Function.comp_apply, id]
    exact cellPtInv_cellPt hp.2.1.1 hp.2.1.2
  rw [hA, Measure.map_smul, Measure.map_map (measurable_cellPtInv c) (measurable_cellPt c),
    Measure.map_congr hae, Measure.map_id]

end UnforcedLeray.Short.PartIIIb.NearInst.Masked
