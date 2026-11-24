import UnforcedLeray.Lib.TrainB.P0ProjectedLinearSeedMild
import UnforcedLeray.Lib.TrainB.P0H3FixOfComponents

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open Set

namespace UnforcedLeray.TrainB

/-- If every ordered derivative of a bounded continuous H³ seed is already weakly solenoidal,
the actual projected mild construction has that seed itself as its linear term. -/
theorem exists_short_solenoidalSeed_mild_train {c ν R : ℝ}
    (hc : 0 < c) (hc1 : 1 ≤ c) (hν : 0 < ν) (hR : 0 ≤ R)
    (H : ContinuousMap ℝ (VectorH3 c))
    (hbound : ∀ t, ‖H t‖ ≤ R / 2)
    (hzero : H 0 = datumVecH3 hc)
    (hdiv : ∀ t α, vecH3CellDerivCLM α (H t) ∈ Cyl.divFree c) :
    ∃ T : ℝ, ∃ hT : 0 < T,
      ∃ u : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c),
        ‖u‖ ≤ R ∧
        u = (H.comp compactTimeInclusion) +
          projectedNonlinearDuhamelCompactMap hc hc1 hν hT.le u ∧
        (∀ t, P0H3CLM hc (u t) = u t) ∧
        vecH3CellDerivCLM Sob.Idx.zero (u (compactEvolutionZero hT)) =
          (memLp_datum_word_derivative hc Sob.Idx.zero).toLp (Train.datum c) ∧
        (∀ v : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c),
          ‖v‖ ≤ R →
          v = (H.comp compactTimeInclusion) +
            projectedNonlinearDuhamelCompactMap hc hc1 hν hT.le v → v = u) := by
  have hfixed : ∀ t, P0H3CLM hc (H t) = H t := by
    intro t
    exact P0H3CLM_eq_self_of_components_divFree hc (H t) (hdiv t)
  obtain ⟨T, hT, u, hu, hfix, husol, htrace, huniq⟩ :=
    exists_short_projectedLinearSeed_mild_train hc hc1 hν hR H hbound hzero
  refine ⟨T, hT, u, hu, ?_, husol, htrace, ?_⟩
  · apply ContinuousMap.ext
    intro t
    have hp : u t = P0H3CLM hc (H t) +
        projectedNonlinearDuhamelCompactMap hc hc1 hν hT.le u t := by
      simpa only [Pi.add_apply] using congrFun hfix t
    change u t = H t + projectedNonlinearDuhamelCompactMap hc hc1 hν hT.le u t
    rw [hfixed t] at hp
    exact hp
  · intro v hv hfv
    apply huniq v hv
    funext t
    have hp : v t = H t +
        projectedNonlinearDuhamelCompactMap hc hc1 hν hT.le v t := by
      simpa [compactTimeInclusion] using
        congrArg (fun f : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c) => f t) hfv
    rw [← hfixed t] at hp
    change v t = P0H3CLM hc (H t) +
      projectedNonlinearDuhamelCompactMap hc hc1 hν hT.le v t
    exact hp

#print axioms UnforcedLeray.TrainB.exists_short_solenoidalSeed_mild_train

end UnforcedLeray.TrainB
