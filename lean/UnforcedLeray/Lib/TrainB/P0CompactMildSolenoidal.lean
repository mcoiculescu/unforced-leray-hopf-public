import UnforcedLeray.Lib.TrainB.P0CompactMildInitialTrace
import UnforcedLeray.Lib.TrainB.P0H3Range
import UnforcedLeray.Lib.TrainB.ProjectedInitialDatum

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory Set

namespace UnforcedLeray.TrainB

/-- The actual nonlinear Duhamel map is fixed by the H³ cylinder Leray projector: its integrand
is the projection of the actual Gaussian heat-divergence response, and the range is closed under
Bochner integration. -/
theorem projectedNonlinearDuhamelCompactMap_fixed_by_P0 {c ν T : ℝ}
    (hc : 0 < c) (hc1 : 1 ≤ c) (hν : 0 < ν) (hT : 0 < T)
    (u : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c))
    (t : Icc (0 : ℝ) T) :
    P0H3CLM hc (projectedNonlinearDuhamelCompactMap hc hc1 hν hT.le u t) =
      projectedNonlinearDuhamelCompactMap hc hc1 hν hT.le u t := by
  by_cases ht : (t : ℝ) = 0
  · rw [projectedNonlinearDuhamelCompactMap_apply]
    simp [projectedHeatNonlinearityIntegral, projectedHeatDuhamelOrbit, ht]
  · have htpos : 0 < (t : ℝ) := lt_of_le_of_ne t.2.1 (Ne.symm ht)
    rw [projectedNonlinearDuhamelCompactMap_apply,
      projectedHeatNonlinearityIntegral]
    let uext : ContinuousMap ℝ (VectorH3 c) := extendCompactPath hT.le u
    let F : ContinuousMap ℝ (TensorH3 c) := tensorH3StressPath hc1 uext
    have hbound : ∀ r ∈ Ioo (0 : ℝ) (t : ℝ), ‖F r‖ ≤ 1536 * ‖u‖ ^ 2 := by
      intro r hr
      dsimp [F]
      exact norm_tensorH3StressPath_extendCompactPath_le hc1 hT.le u r
    have hInt : Integrable (projectedHeatDuhamelOrbit (ν := ν) (s := (t : ℝ)) hc F)
        (volume.restrict (Ioo (0 : ℝ) (t : ℝ))) :=
      integrableOn_projectedHeatDuhamelOrbit hc hν htpos F hbound
    have hIntegral : (P0H3CLM hc) (∫ r, projectedHeatDuhamelOrbit (ν := ν)
        (s := (t : ℝ)) hc F r ∂volume.restrict (Ioo (0 : ℝ) (t : ℝ))) =
        ∫ r, projectedHeatDuhamelOrbit (ν := ν) (s := (t : ℝ)) hc F r
          ∂volume.restrict (Ioo (0 : ℝ) (t : ℝ)) := by
      change (P0H3CLM hc) (∫ r, projectedHeatDuhamelOrbit (ν := ν)
        (s := (t : ℝ)) hc F r ∂volume.restrict (Ioo (0 : ℝ) (t : ℝ))) = _
      rw [← (P0H3CLM hc).integral_comp_comm hInt]
      apply integral_congr_ae
      filter_upwards with r
      exact P0H3CLM_idem hc _
    rw [map_neg]
    exact congrArg Neg.neg hIntegral

/-- If the seed lies in the range of the H³ Leray projector, every affine fixed point of the
actual compact mild map remains in that range at every time. -/
theorem compactActualMildFixedPoint_solenoidal {c ν T : ℝ}
    (hc : 0 < c) (hc1 : 1 ≤ c) (hν : 0 < ν) (hT : 0 < T)
    (g u : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c))
    (hfix : u = g + projectedNonlinearDuhamelCompactMap hc hc1 hν hT.le u)
    (hg : ∀ t, P0H3CLM hc (g t) = g t) :
    ∀ t, P0H3CLM hc (u t) = u t := by
  intro t
  have hduh := projectedNonlinearDuhamelCompactMap_fixed_by_P0 hc hc1 hν hT u t
  have heval : u t = g t + projectedNonlinearDuhamelCompactMap hc hc1 hν hT.le u t := by
    exact congrArg (fun f : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c) => f t) hfix
  calc
    P0H3CLM hc (u t) = P0H3CLM hc
        (g t + projectedNonlinearDuhamelCompactMap hc hc1 hν hT.le u t) := by rw [heval]
    _ = g t + projectedNonlinearDuhamelCompactMap hc hc1 hν hT.le u t := by
      rw [map_add, hg t, hduh]
    _ = u t := heval.symm

/-- If the seed begins at the concrete projected Gaussian H³ datum, the affine fixed point has
exactly the required Gaussian Train datum as its centered-cell L² initial value. -/
theorem compactActualMildFixedPoint_actualDatumTrace {c ν T : ℝ}
    (hc : 0 < c) (hc1 : 1 ≤ c) (hν : 0 < ν) (hT : 0 < T)
    (g u : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c))
    (hfix : u = g + projectedNonlinearDuhamelCompactMap hc hc1 hν hT.le u)
    (hg0 : g (compactEvolutionZero hT) = projectedInitialDatumH3 hc) :
    vecH3CellDerivCLM Sob.Idx.zero (u (compactEvolutionZero hT)) =
      (memLp_datum_word_derivative hc Sob.Idx.zero).toLp (Train.datum c) := by
  rw [compactActualMildFixedPoint_initialTrace hc hc1 hν hT g u hfix, hg0]
  exact projectedInitialDatumH3_value hc

#print axioms UnforcedLeray.TrainB.projectedNonlinearDuhamelCompactMap_fixed_by_P0
#print axioms UnforcedLeray.TrainB.compactActualMildFixedPoint_solenoidal
#print axioms UnforcedLeray.TrainB.compactActualMildFixedPoint_actualDatumTrace

end UnforcedLeray.TrainB
