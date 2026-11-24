import UnforcedLeray.Cons.L2.BackgroundConcrete.SelectedProjectedPotentialCellLp
import UnforcedLeray.Cons.L2.BackgroundConcrete.SpatialProductCellHolder

set_option autoImplicit false

noncomputable section

open MeasureTheory
open Set
open scoped ENNReal

namespace UnforcedLeray.Cons.C03.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0412
open UnforcedLeray.RieszLp

local instance dual_q0_ge_one_cell_pair : Fact (1 ≤ conjExp q0E) := ⟨by
  norm_num [PhaseSpace.conjExp, q0E, B0281.q0]⟩

local instance holder_q0_cell_pair : ENNReal.HolderTriple (conjExp q0E) q0E 1 :=
  UnforcedLeray.Sob.holderTriple_conjExp q0E

/-- The actual Newton-gradient correction pairs integrably over a period cell with the selected
joint representative of every phase-space `L^(11/4)` field. -/
theorem integrable_projectedNewtonCorrection_pair_rep_cell {P : ℝ} [Fact (0 < P)]
    {Φ : SpaceTime → CVec3} (hΦ : IsPhaseTest P Φ) (w : Yq P q0E) :
    Integrable (fun z : SpaceTime => dotL
      (ofReV (gradField (fun y => projectedPotentialRePath Φ (z.1, y)) z.2) +
        ofImV (gradField (fun y => projectedPotentialImPath Φ (z.1, y)) z.2))
      (rep w z.1 z.2))
      (volume.restrict (Ioc (0 : ℝ) P ×ˢ (univ : Set Space))) := by
  have hN := memLp_projectedNewtonCorrection_cell hΦ
  change MemLp (fun z : SpaceTime =>
      ofReV (gradField (fun y => projectedPotentialRePath Φ (z.1, y)) z.2) +
        ofImV (gradField (fun y => projectedPotentialImPath Φ (z.1, y)) z.2))
    (conjExp q0E) (volume.restrict (Ioc (0 : ℝ) P ×ˢ (univ : Set Space))) at hN
  have hW := memLp_rep_periodCell q0E_ne_top w
  exact integrable_dotL_of_memLp_holder hN hW

#print axioms integrable_projectedNewtonCorrection_pair_rep_cell

end UnforcedLeray.Cons.C03.Concrete

end
