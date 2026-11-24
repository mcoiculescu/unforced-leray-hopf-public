import UnforcedLeray.Short.PartI.Sub.T02_1_2_2.WeakDerivCell
import UnforcedLeray.Lib.HeatCylinder.HeatVecH3P0Compatibility

/-!
# Part I, task `PartI:T02/1/2/2`, leaf H: `HeatWeakDeriv`

Source of record: `the November 2 reference manuscript`, lines 261-288.
Every centered derivative component of the actual `H³` heat is the centered `L²` heat of the
matching component of the input (`centeredVecH3Derivative_actualHeatVecH3`), so by the bridge
`WeakDerivCell` the heat semigroup preserves the relation "`x'` is the weak `∂_j`-derivative of
`x`".  The identification of the centered derivative class with `vecH3CellDerivCLM` is re-proved
here (the library copy is private).  No `sorry`, `admit`, `axiom` or `native_decide`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec toVec)
open UnforcedLeray.Cyl (Plane cellμ)
open UnforcedLeray.TrainB

private theorem centeredClass_eq_cell {c : ℝ} (α : Sob.Idx 2 3) (x : VectorH3 c) :
    HeatCylinder.centeredVecH3DerivativeClass α x = vecH3CellDerivCLM α x := by
  apply Lp.ext
  have hleft := HeatCylinder.centeredVecH3DerivativeClass_coe_ae α x
  have hMP : MeasurePreserving id (cellμ c)
      (Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ))) := by
    rw [← HeatCylinder.heatVecH3_measure_eq_cell_deriv c]
    exact MeasurePreserving.id _
  have hright := Lp.coeFn_compMeasurePreserving
    ((Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2 α) x) hMP
  have hright' : (vecH3CellDerivCLM α x : Plane → Vec) =ᵐ[cellμ c]
      (Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2 α x : Plane → Vec) := by
    change (Lp.compMeasurePreserving id hMP
      ((Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2 α) x) :
        Lp Vec 2 (cellμ c)) =ᵐ[cellμ c] _
    simpa using hright
  filter_upwards [hleft, hright'] with z hzleft hzright
  exact hzleft.trans hzright.symm

theorem heatWeakDeriv_proof : HeatWeakDeriv := by
  intro c θ hc j x x' h
  by_cases hθ : 0 < θ
  · have h1 := (weakDerivCell_proof c hc j x x').mp h
    rw [HeatCylinder.heatVecH3Semigroup_apply_of_pos hc hθ,
      HeatCylinder.heatVecH3Semigroup_apply_of_pos hc hθ,
      HeatCylinder.actualHeatVecH3CLM_apply, HeatCylinder.actualHeatVecH3CLM_apply]
    refine (weakDerivCell_proof c hc j _ _).mpr ?_
    have e1 : vecH3CellDerivCLM (Sob.Idx.cons j Sob.Idx.zero : Sob.Idx 2 3)
        (HeatCylinder.actualHeatVecH3 hc hθ x) =
        HeatCylinder.centeredHeatVecL2CLM hc θ
          (vecH3CellDerivCLM (Sob.Idx.cons j Sob.Idx.zero : Sob.Idx 2 3) x) := by
      rw [← centeredClass_eq_cell, HeatCylinder.centeredVecH3Derivative_actualHeatVecH3 hc hθ x,
        centeredClass_eq_cell]
    have e2 : vecH3CellDerivCLM (Sob.Idx.zero : Sob.Idx 2 3)
        (HeatCylinder.actualHeatVecH3 hc hθ x') =
        HeatCylinder.centeredHeatVecL2CLM hc θ
          (vecH3CellDerivCLM (Sob.Idx.zero : Sob.Idx 2 3) x') := by
      rw [← centeredClass_eq_cell, HeatCylinder.centeredVecH3Derivative_actualHeatVecH3 hc hθ x',
        centeredClass_eq_cell]
    rw [e1, e2, h1]
  · rw [HeatCylinder.heatVecH3Semigroup_eq_id_of_nonpos hc (not_lt.mp hθ)]
    exact h

end UnforcedLeray.Short.PartI

#print axioms UnforcedLeray.Short.PartI.heatWeakDeriv_proof
