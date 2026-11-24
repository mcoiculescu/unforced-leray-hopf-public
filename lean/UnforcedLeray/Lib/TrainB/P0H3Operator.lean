import UnforcedLeray.Lib.TrainB.P0RoughH3

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory
open scoped ENNReal
open UnforcedLeray.Cyl

namespace UnforcedLeray.TrainB

local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩

/-- The ordered derivative components determine the cylinder H³ graph element. -/
theorem vecH3_eq_of_cellDeriv_eq {c : ℝ} {x y : VecH3 c}
    (h : ∀ α : Sob.Idx 2 3, vecH3CellDerivCLM α x = vecH3CellDerivCLM α y) : x = y := by
  apply Sob.W.ext
  have hzero := h Sob.Idx.zero
  change weightedToCellL2Isometry c
      (Sob.W.value (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec2 3 2 x) =
    weightedToCellL2Isometry c
      (Sob.W.value (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec2 3 2 y) at hzero
  exact (weightedToCellL2Isometry c).injective hzero

/-- A choice of the genuine graph representative of P₀ on H³. -/
noncomputable def P0H3Fun {c : ℝ} (hc : 0 < c) (x : VecH3 c) : VecH3 c :=
  Classical.choose (exists_projectedVecH3 hc x)

theorem P0H3Fun_component {c : ℝ} (hc : 0 < c) (x : VecH3 c)
    (α : Sob.Idx 2 3) :
    vecH3CellDerivCLM α (P0H3Fun hc x) = Cyl.P0 c (vecH3CellDerivCLM α x) :=
  (Classical.choose_spec (exists_projectedVecH3 hc x)).1 α

theorem P0H3Fun_norm_le {c : ℝ} (hc : 0 < c) (x : VecH3 c) :
    ‖P0H3Fun hc x‖ ≤ ‖x‖ := (Classical.choose_spec (exists_projectedVecH3 hc x)).2

/-- The actual cylinder H³ Leray projection as a bounded linear operator, with period-independent
operator norm at most one. -/
noncomputable def P0H3CLM {c : ℝ} (hc : 0 < c) : VecH3 c →L[ℝ] VecH3 c := by
  let L : VecH3 c →ₗ[ℝ] VecH3 c := {
    toFun := P0H3Fun hc
    map_add' := by
      intro x y
      apply vecH3_eq_of_cellDeriv_eq
      intro α
      calc
        vecH3CellDerivCLM α (P0H3Fun hc (x + y)) =
            Cyl.P0 c (vecH3CellDerivCLM α (x + y)) := P0H3Fun_component hc _ α
        _ = Cyl.P0 c (vecH3CellDerivCLM α x) + Cyl.P0 c (vecH3CellDerivCLM α y) := by
              rw [map_add, map_add]
        _ = vecH3CellDerivCLM α (P0H3Fun hc x + P0H3Fun hc y) := by
              rw [map_add, ← P0H3Fun_component hc x α, ← P0H3Fun_component hc y α]
    map_smul' := by
      intro a x
      apply vecH3_eq_of_cellDeriv_eq
      intro α
      calc
        vecH3CellDerivCLM α (P0H3Fun hc (a • x)) =
            Cyl.P0 c (vecH3CellDerivCLM α (a • x)) := P0H3Fun_component hc _ α
        _ = a • Cyl.P0 c (vecH3CellDerivCLM α x) := by rw [map_smul, map_smul]
        _ = vecH3CellDerivCLM α (a • P0H3Fun hc x) := by
              rw [map_smul, ← P0H3Fun_component hc x α]
  }
  exact L.mkContinuous 1 (fun x => by
    change ‖P0H3Fun hc x‖ ≤ (1 : ℝ) * ‖x‖
    rw [one_mul]
    exact P0H3Fun_norm_le hc x)

theorem P0H3CLM_apply_component {c : ℝ} (hc : 0 < c) (x : VecH3 c)
    (α : Sob.Idx 2 3) :
    vecH3CellDerivCLM α (P0H3CLM hc x) = Cyl.P0 c (vecH3CellDerivCLM α x) := by
  simpa [P0H3CLM] using P0H3Fun_component hc x α

#print axioms UnforcedLeray.TrainB.P0H3Fun_component
#print axioms UnforcedLeray.TrainB.P0H3Fun_norm_le
#print axioms UnforcedLeray.TrainB.P0H3CLM_apply_component

end UnforcedLeray.TrainB
