import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.HkStep.Energy.Dyn.Defs
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_1_2_1_3_3
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.End.Leaf.PdCxPeriodic
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.End.Leaf.IbpPdCxWeak

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

theorem smoothCellJet : UnforcedLeray.Short.IIIa.SmoothCellJet := by
  intro c m F hc hF hper hmem k
  have hpd : ∀ w : List (Fin 2), ∀ x : ℝ × ℝ,
      adjSpatial w F (x.1 + c, x.2) = adjSpatial w F x := by
    intro w
    induction w with
    | nil => exact hper
    | cons j w ih =>
      intro x
      show pdCx j (adjSpatial w F) (x.1 + c, x.2) = pdCx j (adjSpatial w F) x
      exact pdCxPeriodic c j (adjSpatial w F) (contDiff_adjSpatial hF w) ih x
  exact {
    base := rfl
    periodic := fun w _ x => hpd w x
    memX := fun w _ => hmem w
    deriv := fun j w _ => ibpPdCxWeak c j (adjSpatial w F) hc (contDiff_adjSpatial hF w) (hpd w) }

end UnforcedLeray.Short.IIIa
