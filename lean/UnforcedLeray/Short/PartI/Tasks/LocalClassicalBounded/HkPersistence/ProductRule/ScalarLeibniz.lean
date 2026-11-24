import UnforcedLeray.Short.PartI.Sub.PartI_T02_1_2_3_1
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.HkPersistence.ProductRule.ScalarLeibniz.WeakClosed
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.HkPersistence.ProductRule.ScalarLeibniz.SmoothApprox

/-!
# Part I, task `PartI:T02/1/2/3/1`: cylinder Leibniz rule for `scalarH3Mul`

Source of record: `the November 2 reference manuscript`, lines 261-288.

Composes the two leaves `bdp_weakClosed` (`PartI:T02/1/2/3/1/1`) and `bdp_smoothApprox`
(`PartI:T02/1/2/3/1/2`) through `bdp_scalar_leibniz_of`.
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

theorem bdp_scalar_leibniz {c : ℝ} (hc1 : 1 ≤ c) (j : Fin 2) (x x' y y' : ScalarH3 c) :
    Sob.HasWeakDeriv (Sob.cylinder c) [(Sob.cylinder c).dir j]
      (Cyl.H.val x : Plane → ℝ) (Cyl.H.val x' : Plane → ℝ) →
    Sob.HasWeakDeriv (Sob.cylinder c) [(Sob.cylinder c).dir j]
      (Cyl.H.val y : Plane → ℝ) (Cyl.H.val y' : Plane → ℝ) →
    Sob.HasWeakDeriv (Sob.cylinder c) [(Sob.cylinder c).dir j]
      (Cyl.H.val (scalarH3Mul hc1 x y) : Plane → ℝ)
      (Cyl.H.val (scalarH3Mul hc1 x' y + scalarH3Mul hc1 x y') : Plane → ℝ) :=
  bdp_scalar_leibniz_of bdp_weakClosed bdp_smoothApprox hc1 j x x' y y'

end UnforcedLeray.Short.PartI
