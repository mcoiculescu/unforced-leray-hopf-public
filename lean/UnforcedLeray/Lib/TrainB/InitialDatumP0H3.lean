import UnforcedLeray.Lib.TrainB.InitialDatumSolenoidal
import UnforcedLeray.Lib.TrainB.P0H3Range

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory
open scoped ENNReal
open UnforcedLeray.Cyl

namespace UnforcedLeray.TrainB

/-- The zero-word centered-cell component of the H³ datum is its actual L² class. -/
theorem vecH3CellDeriv_zero_datum {c : ℝ} (hc : 0 < c) :
    vecH3CellDerivCLM Sob.Idx.zero (datumVecH3 hc) =
      (memLp_datum_word_derivative hc Sob.Idx.zero).toLp (Train.datum c) := by
  change weightedToCellL2Isometry c
      (Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ))
        ℝ Vec2 3 2 Sob.Idx.zero (datumVecH3 hc)) = _
  rw [Sob.W.deriv_zero]
  let hMP : MeasurePreserving id (Cyl.cellμ c)
      (Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ))) := by
    rw [← vecH1_measure_eq_cell c]
    exact MeasurePreserving.id _
  change (Lp.compMeasurePreservingₗᵢ ℝ id hMP)
      (Sob.W.value (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec2 3 2
        (datumVecH3 hc)) = _
  apply Lp.ext
  have hcomp := Lp.coeFn_compMeasurePreserving
    (Sob.W.value (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec2 3 2
      (datumVecH3 hc)) hMP
  have hvalue := datumVecH3_value_ae hc
  have hmem := memLp_datum_word_derivative hc Sob.Idx.zero
  have hdata : (memLp_datum_word_derivative hc Sob.Idx.zero).toLp
      (Train.datum c) =ᵐ[Cyl.cellμ c] Train.datum c := by
    have hzero :
        Sob.iterD ((Sob.cylinder c).word (Sob.Idx.zero : Sob.Idx 2 3)) (Train.datum c) = Train.datum c := by
      simp [Sob.TestDomain.word_zero, Sob.iterD]
    filter_upwards [hmem.coeFn_toLp] with z hz
    simpa only [hzero] using hz
  filter_upwards [hcomp, hvalue, hdata] with z hzComp hzValue hzData
  calc
    ((Lp.compMeasurePreserving id hMP
        (Sob.W.value (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec2 3 2
          (datumVecH3 hc)) : L2v c) z) =
        (Sob.W.value (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec2 3 2
          (datumVecH3 hc) : Lp Vec2 2
            (Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ)))) z := by
              simpa [Function.comp_id] using hzComp
    _ = Train.datum c z := hzValue
    _ = (memLp_datum_word_derivative hc Sob.Idx.zero).toLp (Train.datum c) z := hzData.symm

/-- The H³ projection of the actual datum has the same centered-cell L² value as the datum.
This is the initial-trace identity needed for a solenoidal projected linear seed. -/
theorem P0H3_datum_value_eq_datum {c : ℝ} (hc : 0 < c) :
    vecH3CellDerivCLM Sob.Idx.zero (P0H3CLM hc (datumVecH3 hc)) =
      (memLp_datum_word_derivative hc Sob.Idx.zero).toLp (Train.datum c) := by
  rw [P0H3CLM_apply_component, vecH3CellDeriv_zero_datum]
  exact P0_datum_eq_datum hc

#print axioms UnforcedLeray.TrainB.vecH3CellDeriv_zero_datum
#print axioms UnforcedLeray.TrainB.P0H3_datum_value_eq_datum

end UnforcedLeray.TrainB
