import UnforcedLeray.Lib.HeatCylinder.HeatVecH3DerivativeComponentsRough
import UnforcedLeray.Lib.HeatCylinder.HeatVecGaussianAverageIdentification
import UnforcedLeray.Lib.HeatCylinder.HeatVecL2NormalizedCenteredInverse
import UnforcedLeray.Lib.TrainB.P0H3Range

/-!
# Actual ordinary H³ heat preserves and commutes with the cylinder Leray projection

Each centered H³ derivative is the centered actual L² heat of the matching derivative input.
The actual centered heat commutes with P₀, and TrainB's H³ projection acts componentwise by P₀;
these concrete identities give commutation on the whole H³ graph.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.Train (Vec)
open UnforcedLeray.Cyl (L2v cellμ)

private theorem centeredVecH3DerivativeClass_eq_vecH3CellDerivCLM_local
    {c : ℝ} (α : UnforcedLeray.Sob.Idx 2 3)
    (x : UnforcedLeray.Cyl.H ℝ Vec c 0 3) :
    centeredVecH3DerivativeClass α x =
      UnforcedLeray.TrainB.vecH3CellDerivCLM α x := by
  apply Lp.ext
  have hleft := centeredVecH3DerivativeClass_coe_ae α x
  have hMP : MeasurePreserving id (cellμ c)
      (UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))) := by
    rw [← heatVecH3_measure_eq_cell_deriv c]
    exact MeasurePreserving.id _
  have hright := Lp.coeFn_compMeasurePreserving
    ((UnforcedLeray.Sob.W.deriv (UnforcedLeray.Sob.cylinder c)
      (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2 α) x) hMP
  have hright' : (UnforcedLeray.TrainB.vecH3CellDerivCLM α x : Plane → Vec) =ᵐ[
      cellμ c] (UnforcedLeray.Sob.W.deriv (UnforcedLeray.Sob.cylinder c)
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2 α x : Plane → Vec) := by
    change (Lp.compMeasurePreserving id hMP
      ((UnforcedLeray.Sob.W.deriv (UnforcedLeray.Sob.cylinder c)
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2 α) x) :
        Lp Vec 2 (cellμ c)) =ᵐ[cellμ c] _
    simpa using hright
  filter_upwards [hleft, hright'] with z hzleft hright
  calc
    (centeredVecH3DerivativeClass α x : Plane → Vec) z =
        (UnforcedLeray.Sob.W.deriv (UnforcedLeray.Sob.cylinder c)
          (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2 α x : Plane → Vec) z := hzleft
    _ = (UnforcedLeray.TrainB.vecH3CellDerivCLM α x : Plane → Vec) z := by
      exact hright.symm

/-- Every centered derivative component of the actual H³ heat is the actual centered L² heat
of the matching centered input derivative. -/
theorem centeredVecH3Derivative_actualHeatVecH3 {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    (x : UnforcedLeray.Cyl.H ℝ Vec c 0 3)
    (α : UnforcedLeray.Sob.Idx 2 3) :
    centeredVecH3DerivativeClass α (actualHeatVecH3 hc hθ x) =
      centeredHeatVecL2CLM hc θ (centeredVecH3DerivativeClass α x) := by
  have hnorm := vectorH3DerivativeNormalizedValue_actualHeatVecH3 hc hθ x α
  have hinv (y : L2v c) :
      normalizedVecToCenteredCLM hc (centeredVecToNormalizedCLM hc y) = y := by
    change normalizedVecToCenteredLinear hc (centeredVecToNormalizedLinear hc y) = y
    exact normalizedVecToCenteredLinear_centeredVecToNormalizedLinear hc y
  calc
    centeredVecH3DerivativeClass α (actualHeatVecH3 hc hθ x) =
        normalizedVecToCenteredCLM hc
          (vectorH3DerivativeNormalizedValue hc α (actualHeatVecH3 hc hθ x)) :=
            (hinv _).symm
    _ = normalizedVecToCenteredCLM hc
        (heatVecL2CLM hc θ (vectorH3DerivativeNormalizedValue hc α x)) :=
          congrArg (normalizedVecToCenteredCLM hc) hnorm
    _ = centeredHeatVecL2CLM hc θ (centeredVecH3DerivativeClass α x) := rfl

/-- The actual ordinary Gaussian heat on centered H³ commutes with the actual TrainB Leray
projection at every positive age. -/
theorem actualHeatVecH3_P0H3CLM_comm {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    (x : UnforcedLeray.TrainB.VectorH3 c) :
    UnforcedLeray.TrainB.P0H3CLM hc (actualHeatVecH3 hc hθ x) =
      actualHeatVecH3 hc hθ (UnforcedLeray.TrainB.P0H3CLM hc x) := by
  apply UnforcedLeray.TrainB.vecH3_eq_of_cellDeriv_eq
  intro α
  have hP0comp := UnforcedLeray.TrainB.P0H3CLM_apply_component hc
  calc
    UnforcedLeray.TrainB.vecH3CellDerivCLM α
        (UnforcedLeray.TrainB.P0H3CLM hc (actualHeatVecH3 hc hθ x)) =
      UnforcedLeray.Cyl.P0 c
        (UnforcedLeray.TrainB.vecH3CellDerivCLM α (actualHeatVecH3 hc hθ x)) :=
          hP0comp _ α
    _ =
      UnforcedLeray.Cyl.P0 c
        (centeredVecH3DerivativeClass α (actualHeatVecH3 hc hθ x)) := by
          rw [centeredVecH3DerivativeClass_eq_vecH3CellDerivCLM_local α]
    _ = UnforcedLeray.Cyl.P0 c
        (centeredHeatVecL2CLM hc θ (centeredVecH3DerivativeClass α x)) := by
          rw [centeredVecH3Derivative_actualHeatVecH3 hc hθ x α]
    _ = centeredHeatVecL2CLM hc θ
        (UnforcedLeray.Cyl.P0 c (centeredVecH3DerivativeClass α x)) :=
          (centeredHeatVecL2CLM_P0_comm_actual hc hθ
            (centeredVecH3DerivativeClass α x)).symm
    _ = centeredHeatVecL2CLM hc θ
        (UnforcedLeray.TrainB.vecH3CellDerivCLM α
          (UnforcedLeray.TrainB.P0H3CLM hc x)) := by
          have hP0center :
              UnforcedLeray.TrainB.vecH3CellDerivCLM α
                (UnforcedLeray.TrainB.P0H3CLM hc x) =
              UnforcedLeray.Cyl.P0 c (centeredVecH3DerivativeClass α x) := by
            calc
              _ = UnforcedLeray.Cyl.P0 c
                    (UnforcedLeray.TrainB.vecH3CellDerivCLM α x) := hP0comp x α
              _ = UnforcedLeray.Cyl.P0 c (centeredVecH3DerivativeClass α x) :=
                    congrArg (UnforcedLeray.Cyl.P0 c)
                      (centeredVecH3DerivativeClass_eq_vecH3CellDerivCLM_local α x).symm
          exact congrArg (centeredHeatVecL2CLM hc θ) hP0center.symm
    _ = centeredVecH3DerivativeClass α
        (actualHeatVecH3 hc hθ (UnforcedLeray.TrainB.P0H3CLM hc x)) := by
          calc
            _ = centeredHeatVecL2CLM hc θ
                (centeredVecH3DerivativeClass α
                  (UnforcedLeray.TrainB.P0H3CLM hc x)) := by
                    exact congrArg (centeredHeatVecL2CLM hc θ)
                      (centeredVecH3DerivativeClass_eq_vecH3CellDerivCLM_local α
                        (UnforcedLeray.TrainB.P0H3CLM hc x)).symm
            _ = centeredVecH3DerivativeClass α
                (actualHeatVecH3 hc hθ (UnforcedLeray.TrainB.P0H3CLM hc x)) :=
                  (centeredVecH3Derivative_actualHeatVecH3 hc hθ
                    (UnforcedLeray.TrainB.P0H3CLM hc x) α).symm
    _ = UnforcedLeray.TrainB.vecH3CellDerivCLM α
        (actualHeatVecH3 hc hθ (UnforcedLeray.TrainB.P0H3CLM hc x)) :=
          centeredVecH3DerivativeClass_eq_vecH3CellDerivCLM_local α _

end UnforcedLeray.HeatCylinder

#print axioms UnforcedLeray.HeatCylinder.centeredVecH3Derivative_actualHeatVecH3
#print axioms UnforcedLeray.HeatCylinder.actualHeatVecH3_P0H3CLM_comm
