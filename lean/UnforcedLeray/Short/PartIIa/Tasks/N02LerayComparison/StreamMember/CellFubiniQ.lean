import UnforcedLeray.Short.PartIIa.Sub.N02_2
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.StreamMember.CellFubiniEta

/-!


Source of record: `the November 2 reference manuscript`, lines 1730-1732.
Target: `CellFubiniQ` (`Sub/N02_2.lean`): for `G` integrable on `cell c = Ioi 0 ×ˢ (Ioc 0 c ×ˢ univ)`,
the cell integral is `∫ s ∈ (0,∞), ∫ η, ∫ q ∈ (0,c], G (s, q, η)`.

Route: rewrite the cell integral with `cellFubiniEta` (order `(s, q, η)`). For almost every `s`,
the slice `(q, η) ↦ G (s, q, η)` is integrable on `Ioc 0 c ×ˢ univ`
(`Integrable.prod_right_ae` on the product of restricted measures), so `integral_integral_swap`
exchanges the inner `q` and `η` integrals.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226

/-- **Fubini on the cell, order `(s, η, q)`** (task `PartII-a:N02/2/11`; the statement is the
unchanged `CellFubiniQ` of `Sub/N02_2.lean`). -/
theorem cellFubiniQ : UnforcedLeray.Short.PartIIa.CellFubiniQ := by
  intro c G hG
  have hvol : (volume : Measure Profile) =
      (volume : Measure ℝ).prod ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
    rw [Measure.volume_eq_prod ℝ (ℝ × ℝ), Measure.volume_eq_prod ℝ ℝ]
  have hcell : cell c = Ioi (0 : ℝ) ×ˢ (Ioc (0 : ℝ) c ×ˢ (univ : Set ℝ)) := rfl
  -- the cell measure as a product of restricted measures
  have hmeas : (volume : Measure Profile).restrict (cell c) =
      ((volume : Measure ℝ).restrict (Ioi (0 : ℝ))).prod
        (((volume : Measure ℝ).restrict (Ioc (0 : ℝ) c)).prod (volume : Measure ℝ)) := by
    rw [hvol, hcell, ← Measure.prod_restrict, ← Measure.prod_restrict, Measure.restrict_univ]
  have hG2 : Integrable G (((volume : Measure ℝ).restrict (Ioi (0 : ℝ))).prod
      (((volume : Measure ℝ).restrict (Ioc (0 : ℝ) c)).prod (volume : Measure ℝ))) := by
    rw [← hmeas]
    exact hG
  -- for almost every `s`, the slice `(q, η) ↦ G (s, q, η)` is integrable
  have hae := hG2.prod_right_ae
  refine (cellFubiniEta c G hG).trans ?_
  refine integral_congr_ae ?_
  filter_upwards [hae] with s hs
  exact integral_integral_swap (f := fun q η => G (s, (q, η))) hs

end UnforcedLeray.Short.PartIIa
