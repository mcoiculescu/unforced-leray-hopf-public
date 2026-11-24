import UnforcedLeray.Lib.TrainB.P0GaussianBilinear

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open UnforcedLeray.Cyl

namespace UnforcedLeray.TrainB

/-- The H³ Leray operator is idempotent because every ordered component is the actual L²
orthogonal projection. -/
theorem P0H3CLM_idem {c : ℝ} (hc : 0 < c) (x : VectorH3 c) :
    P0H3CLM hc (P0H3CLM hc x) = P0H3CLM hc x := by
  apply vecH3_eq_of_cellDeriv_eq
  intro α
  rw [P0H3CLM_apply_component hc (P0H3CLM hc x) α,
    P0H3CLM_apply_component hc x α, Cyl.P0_idem]

/-- The value component of every H³ Leray output belongs to the actual weakly solenoidal
subspace of centered-cell L². -/
theorem P0H3CLM_value_mem_divFree {c : ℝ} (hc : 0 < c) (x : VectorH3 c) :
    vecH3CellDerivCLM Sob.Idx.zero (P0H3CLM hc x) ∈ Cyl.divFree c := by
  rw [P0H3CLM_apply_component]
  exact Cyl.P0_mem _

#print axioms UnforcedLeray.TrainB.P0H3CLM_idem
#print axioms UnforcedLeray.TrainB.P0H3CLM_value_mem_divFree

end UnforcedLeray.TrainB
