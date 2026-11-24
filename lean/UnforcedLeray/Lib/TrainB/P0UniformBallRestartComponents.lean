import UnforcedLeray.Lib.TrainB.P0UniformBallRestart

set_option autoImplicit false

noncomputable section

open Set UnforcedLeray.Cyl

namespace UnforcedLeray.TrainB

/-- Uniformly bounded P₀-fixed initial states produce local mild trajectories whose every
ordered centered-cell derivative has the same uniform bound throughout the common interval. -/
theorem exists_uniform_short_projected_mild_train_on_P0_ball_components
    {c ν M : ℝ} (hc : 0 < c) (hc1 : 1 ≤ c) (hν : 0 < ν) (hM : 0 ≤ M) :
    ∃ T : ℝ, ∃ hT : 0 < T,
      ∀ x : VectorH3 c, ‖x‖ ≤ M → P0H3CLM hc x = x →
        ∃ u : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c),
          ‖u‖ ≤ 2 * M ∧
          u = (projectedHeatSeedPath hc hν x).comp compactTimeInclusion +
            projectedNonlinearDuhamelCompactMap hc hc1 hν hT.le u ∧
          (∀ t, P0H3CLM hc (u t) = u t) ∧
          u (compactEvolutionZero hT) = x ∧
          (∀ t : Icc (0 : ℝ) T, ∀ α : Sob.Idx 2 3,
            ‖vecH3CellDerivCLM α (u t)‖ ≤ 2 * M) ∧
          (∀ v : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c),
            ‖v‖ ≤ 2 * M →
            v = (projectedHeatSeedPath hc hν x).comp compactTimeInclusion +
              projectedNonlinearDuhamelCompactMap hc hc1 hν hT.le v → v = u) := by
  obtain ⟨T, hT, hx⟩ := exists_uniform_short_projected_mild_train_on_P0_ball hc hc1 hν hM
  refine ⟨T, hT, fun x hxnorm hxP0 => ?_⟩
  obtain ⟨u, hu, hfix, hsol, htrace, huniq⟩ := hx x hxnorm hxP0
  refine ⟨u, hu, hfix, hsol, htrace, ?_, huniq⟩
  intro t α
  calc
    ‖vecH3CellDerivCLM α (u t)‖ ≤ ‖u t‖ := vecH3CellDeriv_norm_le α (u t)
    _ ≤ ‖u‖ := u.norm_coe_le_norm t
    _ ≤ 2 * M := hu

#print axioms UnforcedLeray.TrainB.exists_uniform_short_projected_mild_train_on_P0_ball_components

end UnforcedLeray.TrainB
