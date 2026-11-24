import UnforcedLeray.Short.PartI.Sub.T02_1_2_2.P0WeakDeriv

/-!
# Part I, task `PartI:T02/1/2/3/4`: `P₀` commutes with the weak `∂_j` on `H³`

Source of record: `the November 2 reference manuscript`, lines 261-288.
This is `p0WeakDeriv_proof` (Short/PartI/Sub/T02_1_2_2/P0WeakDeriv.lean), unfolded.
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

theorem bdp_P0_hasWeakDeriv {c : ℝ} (hc : 0 < c) (j : Fin 2) (x x' : VectorH3 c) :
    Sob.HasWeakDeriv (Sob.cylinder c) [(Sob.cylinder c).dir j]
      (Cyl.H.val x : Plane → Vec) (Cyl.H.val x' : Plane → Vec) →
    Sob.HasWeakDeriv (Sob.cylinder c) [(Sob.cylinder c).dir j]
      (Cyl.H.val (P0H3CLM hc x) : Plane → Vec) (Cyl.H.val (P0H3CLM hc x') : Plane → Vec) :=
  p0WeakDeriv_proof c hc j x x'

end UnforcedLeray.Short.PartI

#print axioms UnforcedLeray.Short.PartI.bdp_P0_hasWeakDeriv
