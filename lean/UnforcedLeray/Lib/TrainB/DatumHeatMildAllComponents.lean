import UnforcedLeray.Lib.TrainB.DatumHeatSolenoidalMild

set_option autoImplicit false

noncomputable section

open Set

namespace UnforcedLeray.TrainB

/-- Every ordered component of an H³ state fixed by the actual componentwise Leray map lies in
the corresponding weakly solenoidal L² range. -/
theorem components_divFree_of_P0H3CLM_fixed {c : ℝ} (hc : 0 < c)
    (x : VectorH3 c) (hfix : P0H3CLM hc x = x) :
    ∀ α : Sob.Idx 2 3, vecH3CellDerivCLM α x ∈ Cyl.divFree c := by
  intro α
  rw [← hfix, P0H3CLM_apply_component]
  exact Cyl.P0_mem _

/-- The actual datum-seeded local mild solution has weakly solenoidal value and every ordered H³
derivative at every time, in addition to the literal nonlinear mild equation and uniqueness. -/
theorem exists_short_datumHeat_mild_allComponentsDivFree {c ν : ℝ}
    (hc2 : 2 ≤ c) (hν : 0 < ν) :
    ∃ T : ℝ, ∃ hT : 0 < T,
      ∃ u : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c),
        ‖u‖ ≤ 2 * ‖datumVecH3 (by linarith : 0 < c)‖ ∧
        u = (datumHeatSeedPath (by linarith : 0 < c) hν |>.comp compactTimeInclusion) +
          projectedNonlinearDuhamelCompactMap (by linarith : 0 < c)
            (by linarith : 1 ≤ c) hν (le_of_lt hT) u ∧
        (∀ t α, vecH3CellDerivCLM α (u t) ∈ Cyl.divFree c) ∧
        vecH3CellDerivCLM Sob.Idx.zero (u (compactEvolutionZero hT)) =
          (memLp_datum_word_derivative (by linarith : 0 < c) Sob.Idx.zero).toLp
            (Train.datum c) ∧
        (∀ v : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c),
          ‖v‖ ≤ 2 * ‖datumVecH3 (by linarith : 0 < c)‖ →
          v = (datumHeatSeedPath (by linarith : 0 < c) hν |>.comp compactTimeInclusion) +
            projectedNonlinearDuhamelCompactMap (by linarith : 0 < c)
              (by linarith : 1 ≤ c) hν (le_of_lt hT) v → v = u) := by
  obtain ⟨T, hT, u, hu, hEq, hfix, htrace, huniq⟩ :=
    exists_short_datumHeat_solenoidal_mild_train hc2 hν
  refine ⟨T, hT, u, hu, hEq, ?_, htrace, huniq⟩
  intro t α
  exact components_divFree_of_P0H3CLM_fixed (by linarith : 0 < c) (u t) (hfix t) α

#print axioms UnforcedLeray.TrainB.components_divFree_of_P0H3CLM_fixed
#print axioms UnforcedLeray.TrainB.exists_short_datumHeat_mild_allComponentsDivFree

end UnforcedLeray.TrainB
