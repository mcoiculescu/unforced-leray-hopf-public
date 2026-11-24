import UnforcedLeray.Short.PartIIIa.Sub.T21_c2_2
import UnforcedLeray.Short.PartI.TrainClass

/-!
# Part III-a, task `PartIII-a:T21/c2/2/8` (`FmrVelBdd`): the velocity bound for BUC trains

Source of record: `the November 2 reference manuscript`, lines 270-288
("unique global mild solution in `BUC`"), 283 (`sup_{[0,t]} ‖v‖_∞ < ∞`).

`B0140.IsTrain` carries no bound in the unbounded direction `η` (see `Short/PartI/TrainClass.lean`),
so boundedness of the velocity is not a consequence of its fields; it is a property of the
Gallay-Slijepcevic BUC solution of the source. `FmrVelBdd` (`Sub/T21_c2_2.lean`) therefore carries
`PartI.IsBUCTrain tr` after the train binder; `FmrVelBddBUC` is that one statement, proved here.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology

namespace UnforcedLeray.Short.IIIa

/-- `FmrVelBdd` for trains of the BUC class (the class of the source, SP 270-288): since
`ORG:train-class-IIIa/sub` the statement of `FmrVelBdd` itself. -/
def FmrVelBddBUC : Prop := FmrVelBdd

theorem fmrVelBddBUC : FmrVelBddBUC := by
  intro ν c _ _ tr hbuc T
  obtain ⟨M, hM⟩ := hbuc.sup_bound (S := max T 0) (le_max_right _ _)
  refine ⟨2 * M, fun σ hσ x => ?_⟩
  have hσ' : σ ∈ Icc (0 : ℝ) (max T 0) := ⟨hσ.1, hσ.2.trans (le_max_left _ _)⟩
  have h := hM σ hσ' x
  have h0 : |tr.v σ x 0| ≤ ‖tr.v σ x‖ := by
    simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (tr.v σ x) 0
  have h1 : |tr.v σ x 1| ≤ ‖tr.v σ x‖ := by
    simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (tr.v σ x) 1
  linarith

end UnforcedLeray.Short.IIIa
