import UnforcedLeray.Short.PartI.Sub.PartI_T02_1_4_6_4_1_1_6_Bridges

/-!
# Bridge 2b: the zero-order centered class of an H³ vector field

Proves `VecH3ZeroClassValueAE` (Bridges file, Bridge 2b). Source lines 261-288 of
`the November 2 reference manuscript`. The argument is the body of the private
lemma `centeredVecH3DerivativeClass_eq_vecH3CellDerivCLM_local`
(`Lib/HeatCylinder/HeatVecH3P0Compatibility.lean:27`), restated here for the cell class
`vecH3CellDerivCLM Idx.zero`, together with `W.deriv_zero` (the zero derivative is the value).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter
open scoped Topology ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec toVec)
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.TrainB
open UnforcedLeray.HeatCylinder

/-- Bridge 2b, as the theorem `vecH3ZeroClassValueAE`. -/
theorem vecH3ZeroClassValueAE : VecH3ZeroClassValueAE := by
  intro c x
  have hMP : MeasurePreserving id (UnforcedLeray.Cyl.cellμ c)
      (UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))) := by
    rw [← heatVecH3_measure_eq_cell_deriv c]
    exact MeasurePreserving.id _
  have hright := Lp.coeFn_compMeasurePreserving
    ((UnforcedLeray.Sob.W.deriv (UnforcedLeray.Sob.cylinder c)
      (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2 UnforcedLeray.Sob.Idx.zero) x) hMP
  have hleft : ((vecH3CellDerivCLM UnforcedLeray.Sob.Idx.zero x : Cyl.L2v c) : Plane → Vec)
      =ᵐ[UnforcedLeray.Cyl.cellμ c]
      (UnforcedLeray.Sob.W.deriv (UnforcedLeray.Sob.cylinder c)
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2 UnforcedLeray.Sob.Idx.zero x : Plane → Vec) := by
    change (Lp.compMeasurePreserving id hMP
      ((UnforcedLeray.Sob.W.deriv (UnforcedLeray.Sob.cylinder c)
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2 UnforcedLeray.Sob.Idx.zero) x) :
        Lp Vec 2 (UnforcedLeray.Cyl.cellμ c)) =ᵐ[UnforcedLeray.Cyl.cellμ c] _
    simpa using hright
  have hdz : (UnforcedLeray.Sob.W.deriv (UnforcedLeray.Sob.cylinder c)
      (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2 UnforcedLeray.Sob.Idx.zero x : Plane → Vec)
      =ᵐ[UnforcedLeray.Cyl.cellμ c]
      (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2 x : Plane → Vec) :=
    Filter.Eventually.of_forall fun z => by
      rw [UnforcedLeray.Sob.W.deriv_zero]
  exact hleft.trans hdz

end UnforcedLeray.Short.PartI
