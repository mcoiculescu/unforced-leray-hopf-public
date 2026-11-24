import UnforcedLeray.Lib.TrainB.DatumHeatAgeEnvelope

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open Set UnforcedLeray.Cyl

namespace UnforcedLeray.TrainB

/-- The actual local projected mild train witness has an explicit centered-cell bound for every
ordered derivative, uniform on its full construction interval. -/
theorem exists_short_datumHeat_projected_mild_train_component_envelope
    {c ν : ℝ} (hc2 : 2 ≤ c) (hν : 0 < ν) :
    ∃ T : ℝ, ∃ hT : 0 < T,
      ∃ u : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c),
        ‖u‖ ≤ 2 * ‖datumVecH3 (by linarith : 0 < c)‖ ∧
        u = (fun t : Icc (0 : ℝ) T =>
            P0H3CLM (by linarith : 0 < c)
              (datumHeatSeedPath (by linarith : 0 < c) hν t)) +
          projectedNonlinearDuhamelCompactMap (by linarith : 0 < c)
            (by linarith : 1 ≤ c) hν hT.le u ∧
        (∀ t, P0H3CLM (by linarith : 0 < c) (u t) = u t) ∧
        vecH3CellDerivCLM Sob.Idx.zero (u (compactEvolutionZero hT)) =
          (memLp_datum_word_derivative (by linarith : 0 < c) Sob.Idx.zero).toLp
            (Train.datum c) ∧
        (∀ t : Icc (0 : ℝ) T, ∀ α : Sob.Idx 2 3,
          ‖vecH3CellDerivCLM α (u t)‖ ≤
            2 * ‖datumVecH3 (by linarith : 0 < c)‖) ∧
        (∀ v : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c),
          ‖v‖ ≤ 2 * ‖datumVecH3 (by linarith : 0 < c)‖ →
          v = (fun t : Icc (0 : ℝ) T =>
              P0H3CLM (by linarith : 0 < c)
                (datumHeatSeedPath (by linarith : 0 < c) hν t)) +
            projectedNonlinearDuhamelCompactMap (by linarith : 0 < c)
              (by linarith : 1 ≤ c) hν hT.le v → v = u) := by
  obtain ⟨T, hT, u, hnorm, hfix, hsol, htrace, huniq⟩ :=
    exists_short_datumHeat_projected_mild_train hc2 hν
  refine ⟨T, hT, u, hnorm, hfix, hsol, htrace, ?_, huniq⟩
  intro t α
  calc
    ‖vecH3CellDerivCLM α (u t)‖ ≤ ‖u t‖ := vecH3CellDeriv_norm_le α (u t)
    _ ≤ ‖u‖ := u.norm_coe_le_norm t
    _ ≤ 2 * ‖datumVecH3 (by linarith : 0 < c)‖ := hnorm

#print axioms UnforcedLeray.TrainB.exists_short_datumHeat_projected_mild_train_component_envelope

end UnforcedLeray.TrainB
