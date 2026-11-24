import UnforcedLeray.Short.PartI.Sub.T02_1_2

/-!
# Part I, task `PartI:T02/1/2/3/2`: coordinate components commute with weak derivatives

Source of record: `the November 2 reference manuscript`, lines 261-288.
Components of a vector `H^3` element are weak-derivative-compatible: a weak `∂_j`-derivative
of a vector field gives a weak `∂_j`-derivative of each coordinate, via `Sob.HasWeakDeriv.map_clm`
with the coordinate projection and `vectorH3Component_value_ae`.
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

theorem bdp_vectorH3Component_hasWeakDeriv {c : ℝ} (j i : Fin 2) (x x' : VectorH3 c) :
    Sob.HasWeakDeriv (Sob.cylinder c) [(Sob.cylinder c).dir j]
      (Cyl.H.val x : Plane → Vec) (Cyl.H.val x' : Plane → Vec) →
    Sob.HasWeakDeriv (Sob.cylinder c) [(Sob.cylinder c).dir j]
      (Cyl.H.val (vectorH3Component i x) : Plane → ℝ)
      (Cyl.H.val (vectorH3Component i x') : Plane → ℝ) := by
  intro hx
  have hw := hx.map_clm (EuclideanSpace.proj i : Vec →L[ℝ] ℝ)
  have hf := vectorH3Component_value_ae (c := c) i x
  have hg := vectorH3Component_value_ae (c := c) i x'
  have hμ : (Sob.cylinder c).μ = Cyl.cellμ c := Cyl.cylinder_μ_eq c
  rw [← hμ] at hf hg
  refine hw.congr_ae ?_ ?_
  · filter_upwards [hf] with z hz
    exact hz.symm
  · filter_upwards [hg] with z hz
    exact hz.symm

end UnforcedLeray.Short.PartI
