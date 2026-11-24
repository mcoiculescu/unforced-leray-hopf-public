import UnforcedLeray.Lib.TrainB.P0H3Range

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.TrainB

/-- The componentwise H³ Leray projection fixes any graph element whose every centered-cell
ordered derivative is already in the actual weakly solenoidal subspace. -/
theorem P0H3CLM_eq_self_of_components_divFree {c : ℝ} (hc : 0 < c)
    (x : VectorH3 c)
    (hdiv : ∀ α : Sob.Idx 2 3, vecH3CellDerivCLM α x ∈ Cyl.divFree c) :
    P0H3CLM hc x = x := by
  apply vecH3_eq_of_cellDeriv_eq
  intro α
  rw [P0H3CLM_apply_component]
  exact Cyl.P0_eq_self (hdiv α)

#print axioms UnforcedLeray.TrainB.P0H3CLM_eq_self_of_components_divFree

end UnforcedLeray.TrainB
