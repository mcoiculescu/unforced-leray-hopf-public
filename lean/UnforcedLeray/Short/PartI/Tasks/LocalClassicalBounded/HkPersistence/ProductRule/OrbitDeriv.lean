import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.HkPersistence.ProductRule.P0Deriv
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.HkPersistence.ProductRule.HeatDivDeriv

/-!
# Part I, task `PartI:T02/1/2/3/6`: `∂_j` commutes with `G ↦ P₀ (actual heat-divergence orbit)`

Source of record: `the November 2 reference manuscript`, lines 261-288.
For positive age `θ` the actual orbit `actualHeatDivH3Orbit hc G θ` is the bounded operator
`actualHeatDivH3CLM hc hθ` applied to `G`. Composing the weak-derivative statements
`bdp_actualHeatDivH3CLM_hasWeakDeriv` (task 5) and `bdp_P0_hasWeakDeriv` (task 4) gives the claim.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec toVec)
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.TrainB
open UnforcedLeray.HeatCylinder

theorem bdp_orbitWeakDeriv (c : ℝ) (hc : 0 < c) (θ : ℝ) (_hθ : 0 < θ) (j : Fin 2) (G G' : TensorH3 c) : Sob.HasWeakDeriv (Sob.cylinder c) [(Sob.cylinder c).dir j] (Cyl.H.val G : Plane → TensorVal) (Cyl.H.val G' : Plane → TensorVal) → Sob.HasWeakDeriv (Sob.cylinder c) [(Sob.cylinder c).dir j] (Cyl.H.val (P0H3CLM hc (actualHeatDivH3Orbit hc G θ)) : Plane → Vec) (Cyl.H.val (P0H3CLM hc (actualHeatDivH3Orbit hc G' θ)) : Plane → Vec) := by
  intro h
  have hO : ∀ x : TensorH3 c, actualHeatDivH3Orbit hc x θ = actualHeatDivH3CLM hc _hθ x := by
    intro x
    simp [actualHeatDivH3Orbit, _hθ]
  rw [hO G, hO G']
  exact bdp_P0_hasWeakDeriv hc j (actualHeatDivH3CLM hc _hθ G) (actualHeatDivH3CLM hc _hθ G')
    (bdp_actualHeatDivH3CLM_hasWeakDeriv hc _hθ j G G' h)

end UnforcedLeray.Short.PartI

#print axioms UnforcedLeray.Short.PartI.bdp_orbitWeakDeriv
