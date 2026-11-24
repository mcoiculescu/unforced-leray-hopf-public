import UnforcedLeray.Short.PartIIa.Sub.N02_2

/-!


Source of record: `the November 2 reference manuscript`, lines 1730-1732.
Target: `CellFubiniEta` (`Sub/N02_2.lean`). Route: `setIntegral_prod` on the cell
`Ioi 0 ×ˢ (Ioc 0 c ×ˢ univ)`, then, for almost every `s`, `setIntegral_prod` again on the slice
`Ioc 0 c ×ˢ univ`. The slices are integrable for almost every `s` by `Integrable.prod_right_ae`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226

/-- **Fubini on the cell, order `(s, q, η)`** (task `PartII-a:N02/2/10`): the cell integral of
an integrable `G` is the iterated integral with `η` innermost. -/
theorem cellFubiniEta : UnforcedLeray.Short.PartIIa.CellFubiniEta := by
  intro c G hG
  have hvol : (volume : Measure Profile) =
      (volume : Measure ℝ).prod ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
    rw [Measure.volume_eq_prod ℝ (ℝ × ℝ), Measure.volume_eq_prod ℝ ℝ]
  have hcell : cell c = Ioi (0 : ℝ) ×ˢ (Ioc (0 : ℝ) c ×ˢ (univ : Set ℝ)) := rfl
  rw [hvol, hcell] at hG
  rw [hvol, hcell]
  -- the cell measure as a product of restricted measures
  have hG2 : Integrable G (((volume : Measure ℝ).restrict (Ioi (0 : ℝ))).prod
      (((volume : Measure ℝ).prod (volume : Measure ℝ)).restrict
        (Ioc (0 : ℝ) c ×ˢ (univ : Set ℝ)))) := by
    rw [Measure.prod_restrict]
    exact hG
  -- for almost every `s`, the slice `η ↦ G (s, ·)` is integrable on `Ioc 0 c ×ˢ univ`
  have hae := hG2.prod_right_ae
  rw [setIntegral_prod G hG]
  refine integral_congr_ae ?_
  filter_upwards [hae] with s hs
  rw [setIntegral_prod (fun y : ℝ × ℝ => G (s, y)) hs, Measure.restrict_univ]

end UnforcedLeray.Short.PartIIa
