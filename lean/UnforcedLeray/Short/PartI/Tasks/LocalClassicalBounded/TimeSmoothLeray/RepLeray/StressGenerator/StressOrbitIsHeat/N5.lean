import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.TimeSmoothLeray.RepLeray.StressGenerator.StressOrbitIsHeat.Needed

/-!
# N5: zero-order centered class of the H³ value equals the normalized class

Proof of `NeedZeroClassNormalized` from `Needed.lean`. Both sides are `L²(cellμ)` classes whose
representatives agree a.e. on the cell with the Sobolev value `W.value y`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec toVec)
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.TrainB
open UnforcedLeray.HeatCylinder

theorem needZeroClassNormalized : NeedZeroClassNormalized := by
  intro c hc y
  apply Lp.ext
  have hMP : MeasurePreserving id (UnforcedLeray.Cyl.cellμ c)
      (UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))) := by
    rw [← vecH1_measure_eq_cell c]
    exact MeasurePreserving.id _
  have hL : (vecH3CellDerivCLM UnforcedLeray.Sob.Idx.zero y : Plane → Vec) =ᵐ[
      UnforcedLeray.Cyl.cellμ c]
      (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2 y : Plane → Vec) := by
    change (weightedToCellL2Isometry c (UnforcedLeray.Sob.W.deriv (UnforcedLeray.Sob.cylinder c)
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec 3 2 UnforcedLeray.Sob.Idx.zero y) : Plane → Vec)
      =ᵐ[UnforcedLeray.Cyl.cellμ c] _
    rw [UnforcedLeray.Sob.W.deriv_zero]
    exact Lp.coeFn_compMeasurePreserving _ hMP
  -- the normalized representative, periodized, equals the periodic H^3 value a.e. on the cell
  have hP : perLift hc (normalizedVecRep (vectorH3NormalizedValue hc y)) =ᵐ[volume]
      vectorH3PeriodicValueRep hc y := by
    have h12 : normalizedVecRep (vectorH3NormalizedValue hc y) =ᵐ[
        UnforcedLeray.B0284.cellMeasure c] vectorH3PeriodicValueRep hc y :=
      (normalizedVecRep_ae _).trans (vectorH3NormalizedValue_coe_ae hc y)
    have h13 := perLift_congr_ae hc h12
    rw [perLift_eq_self_of_periodic hc (periodic_vectorH3PeriodicValueRep hc y)] at h13
    exact h13
  have hR : ((normalizedVecToCenteredCLM hc (vectorH3NormalizedValue hc y) :
      UnforcedLeray.Cyl.L2v c) : Plane → Vec) =ᵐ[UnforcedLeray.Cyl.cellμ c]
      vectorH3PeriodicValueRep hc y :=
    (centeredVecOfNormalizedVec_coe_ae hc _).trans (ae_restrict_of_ae hP)
  filter_upwards [hL, hR, vectorH3PeriodicValueRep_ae_value hc y] with z h1 h2 h3
  exact h1.trans (h3.symm.trans h2.symm)

end UnforcedLeray.Short.PartI
