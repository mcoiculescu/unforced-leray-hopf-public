import UnforcedLeray.Lib.TrainB.P0CompactMildSolenoidal
import UnforcedLeray.Lib.TrainB.P0CompactMildUniqueness

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open Set

namespace UnforcedLeray.TrainB

/-- The actual projected Gaussian Duhamel construction returns a unique compact-time mild
solution, preserves the Leray range, and has the Gaussian Train datum as its centered-cell initial
velocity, provided the concrete linear seed path has these properties. -/
theorem exists_unique_compact_solenoidal_mild_train {c ν T R : ℝ}
    (hc : 0 < c) (hc1 : 1 ≤ c) (hν : 0 < ν) (hT : 0 < T) (hR : 0 ≤ R)
    (hsmall : projectedHeatNonlinearityLipschitzCoeff ν R * T ^ (1 / 2 : ℝ) ≤ 1 / 2)
    (g : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c))
    (hg : ‖g‖ ≤ R / 2)
    (hsol : ∀ t, P0H3CLM hc (g t) = g t)
    (hg0 : g (compactEvolutionZero hT) = projectedInitialDatumH3 hc) :
    ∃ u : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c),
      ‖u‖ ≤ R ∧
      u = g + projectedNonlinearDuhamelCompactMap hc hc1 hν hT.le u ∧
      (∀ t, P0H3CLM hc (u t) = u t) ∧
      vecH3CellDerivCLM Sob.Idx.zero (u (compactEvolutionZero hT)) =
        (memLp_datum_word_derivative hc Sob.Idx.zero).toLp (Train.datum c) ∧
      (∀ v : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c),
        ‖v‖ ≤ R →
        v = g + projectedNonlinearDuhamelCompactMap hc hc1 hν hT.le v → v = u) := by
  obtain ⟨u, hu, hfix⟩ := exists_compact_actual_mild_fixedPoint
    hc hc1 hν hT hR hsmall g hg
  have huSol := compactActualMildFixedPoint_solenoidal hc hc1 hν hT g u hfix hsol
  have huTrace := compactActualMildFixedPoint_actualDatumTrace hc hc1 hν hT g u hfix hg0
  refine ⟨u, hu, hfix, huSol, huTrace, ?_⟩
  intro v hv hfixv
  exact (compactActualMildFixedPoint_unique hc hc1 hν hT hR hsmall g u v hu hv hfix hfixv).symm

#print axioms UnforcedLeray.TrainB.exists_unique_compact_solenoidal_mild_train

end UnforcedLeray.TrainB
