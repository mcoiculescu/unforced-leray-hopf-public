import UnforcedLeray.Lib.TrainB.P0GlobalSeedMild

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open Set

namespace UnforcedLeray.TrainB

/-- A bounded continuous H³ orbit from the actual datum yields a short-time mild solution when
used through the actual H³ Leray projection. The projection makes the seed solenoidal, and its
zero-order centered-cell value remains the Gaussian Train datum. -/
theorem exists_short_projectedLinearSeed_mild_train {c ν R : ℝ}
    (hc : 0 < c) (hc1 : 1 ≤ c) (hν : 0 < ν) (hR : 0 ≤ R)
    (H : ContinuousMap ℝ (VectorH3 c))
    (hbound : ∀ t, ‖H t‖ ≤ R / 2)
    (hzero : H 0 = datumVecH3 hc) :
    ∃ T : ℝ, ∃ hT : 0 < T,
      ∃ u : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c),
        ‖u‖ ≤ R ∧
        u = (fun t : Icc (0 : ℝ) T =>
            P0H3CLM hc (H t)) +
          projectedNonlinearDuhamelCompactMap hc hc1 hν hT.le u ∧
        (∀ t, P0H3CLM hc (u t) = u t) ∧
        vecH3CellDerivCLM Sob.Idx.zero (u (compactEvolutionZero hT)) =
          (memLp_datum_word_derivative hc Sob.Idx.zero).toLp (Train.datum c) ∧
        (∀ v : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c),
          ‖v‖ ≤ R →
          v = (fun t : Icc (0 : ℝ) T => P0H3CLM hc (H t)) +
            projectedNonlinearDuhamelCompactMap hc hc1 hν hT.le v → v = u) := by
  let g : ContinuousMap ℝ (VectorH3 c) :=
    ⟨fun t => P0H3CLM hc (H t), (P0H3CLM hc).continuous.comp H.continuous⟩
  have hgBound : ∀ t, ‖g t‖ ≤ R / 2 := by
    intro t
    dsimp [g]
    exact (P0H3CLM_apply_norm_le hc (H t)).trans (hbound t)
  have hgSol : ∀ t, P0H3CLM hc (g t) = g t := by
    intro t
    dsimp [g]
    exact P0H3CLM_idem hc (H t)
  have hgZero : g 0 = projectedInitialDatumH3 hc := by
    dsimp [g, projectedInitialDatumH3]
    rw [hzero]
  obtain ⟨T, hT, u, hu, hfix, husol, htrace, huniq⟩ :=
    exists_short_globalSeed_mild_train hc hc1 hν hR g hgBound hgSol hgZero
  refine ⟨T, hT, u, hu, ?_, husol, htrace, ?_⟩
  have hfixFun : (u : Icc (0 : ℝ) T → VectorH3 c) =
      (g.comp compactTimeInclusion : Icc (0 : ℝ) T → VectorH3 c) +
        projectedNonlinearDuhamelCompactMap hc hc1 hν hT.le u :=
    congrArg (fun f : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c) =>
      (f : Icc (0 : ℝ) T → VectorH3 c)) hfix
  calc
    (u : Icc (0 : ℝ) T → VectorH3 c) =
        (g.comp compactTimeInclusion : Icc (0 : ℝ) T → VectorH3 c) +
          projectedNonlinearDuhamelCompactMap hc hc1 hν hT.le u := hfixFun
    _ = (fun t : Icc (0 : ℝ) T => P0H3CLM hc (H t)) +
          projectedNonlinearDuhamelCompactMap hc hc1 hν hT.le u := by
            congr 1
  · intro v hv hfv
    apply huniq v hv
    apply ContinuousMap.ext
    intro t
    have hp := congrFun hfv t
    simpa [g, compactTimeInclusion] using hp

#print axioms UnforcedLeray.TrainB.exists_short_projectedLinearSeed_mild_train

end UnforcedLeray.TrainB
