import UnforcedLeray.Lib.TrainB.P0CompactMildTrain

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open Set

namespace UnforcedLeray.TrainB

/-- A globally continuous bounded P₀-fixed seed path with the actual projected Gaussian datum at
zero generates a unique compact-time solenoidal mild solution on the explicitly selected short
interval. -/
theorem exists_short_globalSeed_mild_train {c ν R : ℝ}
    (hc : 0 < c) (hc1 : 1 ≤ c) (hν : 0 < ν) (hR : 0 ≤ R)
    (g : ContinuousMap ℝ (VectorH3 c))
    (hbound : ∀ t, ‖g t‖ ≤ R / 2)
    (hsol : ∀ t, P0H3CLM hc (g t) = g t)
    (hg0 : g 0 = projectedInitialDatumH3 hc) :
    ∃ T : ℝ, ∃ hT : 0 < T,
      ∃ u : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c),
        ‖u‖ ≤ R ∧
        u = (g.comp compactTimeInclusion) +
          projectedNonlinearDuhamelCompactMap hc hc1 hν hT.le u ∧
        (∀ t, P0H3CLM hc (u t) = u t) ∧
        vecH3CellDerivCLM Sob.Idx.zero (u (compactEvolutionZero hT)) =
          (memLp_datum_word_derivative hc Sob.Idx.zero).toLp (Train.datum c) ∧
        (∀ v : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c),
          ‖v‖ ≤ R →
          v = (g.comp compactTimeInclusion) +
            projectedNonlinearDuhamelCompactMap hc hc1 hν hT.le v → v = u) := by
  obtain ⟨T, hT, hsmall⟩ := exists_train_short_contraction_time hν hR
  let gT : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c) := g.comp compactTimeInclusion
  have hgT : ‖gT‖ ≤ R / 2 := by
    have hnonneg : 0 ≤ R / 2 := by positivity
    rw [ContinuousMap.norm_le _ hnonneg]
    intro t
    simpa [gT, compactTimeInclusion] using hbound (t : ℝ)
  have hgTsol : ∀ t, P0H3CLM hc (gT t) = gT t := by
    intro t
    simpa [gT, compactTimeInclusion] using hsol (t : ℝ)
  have hgTzero : gT (compactEvolutionZero hT) = projectedInitialDatumH3 hc := by
    simpa [gT, compactTimeInclusion, compactEvolutionZero] using hg0
  obtain ⟨u, hu, hfix, husol, hutrace, huniq⟩ :=
    exists_unique_compact_solenoidal_mild_train hc hc1 hν hT hR hsmall gT hgT hgTsol hgTzero
  refine ⟨T, hT, u, hu, ?_, husol, hutrace, ?_⟩
  · simpa [gT] using hfix
  · intro v hv hfv
    apply huniq v hv
    simpa [gT] using hfv

#print axioms UnforcedLeray.TrainB.exists_short_globalSeed_mild_train

end UnforcedLeray.TrainB
