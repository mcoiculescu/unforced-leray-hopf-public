import UnforcedLeray.Lib.TrainB.P0ArbitraryInitialLocalMild

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open Set

namespace UnforcedLeray.TrainB

/-- A single time step works uniformly for every P₀-fixed state in an H³ ball. The restarted
solution has the actual Gaussian seed, actual projected nonlinear Duhamel term, exact initial
state, and uniqueness in the common radius-`2M` ball. This is the uniform local existence input
for a continuation argument under an a priori H³ bound. -/
theorem exists_uniform_short_projected_mild_train_on_P0_ball {c ν M : ℝ}
    (hc : 0 < c) (hc1 : 1 ≤ c) (hν : 0 < ν) (hM : 0 ≤ M) :
    ∃ T : ℝ, ∃ hT : 0 < T,
      ∀ x : VectorH3 c, ‖x‖ ≤ M → P0H3CLM hc x = x →
        ∃ u : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c),
          ‖u‖ ≤ 2 * M ∧
          u = (projectedHeatSeedPath hc hν x).comp compactTimeInclusion +
            projectedNonlinearDuhamelCompactMap hc hc1 hν hT.le u ∧
          (∀ t, P0H3CLM hc (u t) = u t) ∧
          u (compactEvolutionZero hT) = x ∧
          (∀ v : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c),
            ‖v‖ ≤ 2 * M →
            v = (projectedHeatSeedPath hc hν x).comp compactTimeInclusion +
              projectedNonlinearDuhamelCompactMap hc hc1 hν hT.le v → v = u) := by
  let R : ℝ := 2 * M
  have hR : 0 ≤ R := by dsimp [R]; positivity
  obtain ⟨T, hT, hsmall⟩ := exists_train_short_contraction_time hν hR
  refine ⟨T, hT, fun x hxnorm hxP0 => ?_⟩
  let g : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c) :=
    (projectedHeatSeedPath hc hν x).comp compactTimeInclusion
  have hg : ‖g‖ ≤ R / 2 := by
    have hnonneg : 0 ≤ R / 2 := by positivity
    rw [ContinuousMap.norm_le _ hnonneg]
    intro t
    change ‖projectedHeatSeedPath hc hν x (t : ℝ)‖ ≤ R / 2
    calc
      ‖projectedHeatSeedPath hc hν x (t : ℝ)‖ ≤ ‖x‖ :=
        projectedHeatSeedPath_norm_le hc hν x _
      _ ≤ M := hxnorm
      _ = R / 2 := by dsimp [R]; ring
  have hgsol : ∀ t, P0H3CLM hc (g t) = g t := by
    intro t
    change P0H3CLM hc
      (P0H3CLM hc (HeatCylinder.heatVecH3Semigroup (c := c)
        (θ := max 0 (ν * (t : ℝ))) hc x)) = _
    exact P0H3CLM_idem hc _
  have hgzero : g (compactEvolutionZero hT) = x := by
    change projectedHeatSeedPath hc hν x 0 = x
    exact projectedHeatSeedPath_zero_of_P0_fixed hc hν x hxP0
  obtain ⟨u, hu, hfix⟩ := exists_compact_actual_mild_fixedPoint
    hc hc1 hν hT hR hsmall g hg
  have husol := compactActualMildFixedPoint_solenoidal hc hc1 hν hT g u hfix hgsol
  have htrace := compactActualMildFixedPoint_initialTrace hc hc1 hν hT g u hfix
  refine ⟨u, ?_, ?_, husol, ?_, ?_⟩
  · change ‖u‖ ≤ R at hu
    simpa [R] using hu
  · simpa [g] using hfix
  · simpa [hgzero] using htrace
  · intro v hv hfv
    have hvR : ‖v‖ ≤ R := by simpa [R] using hv
    have hfv' : v = g + projectedNonlinearDuhamelCompactMap hc hc1 hν hT.le v := by
      simpa [g] using hfv
    have huniq := compactActualMildFixedPoint_unique hc hc1 hν hT hR hsmall
      g u v hu hvR hfix hfv'
    exact huniq.symm

#print axioms UnforcedLeray.TrainB.exists_uniform_short_projected_mild_train_on_P0_ball

end UnforcedLeray.TrainB
