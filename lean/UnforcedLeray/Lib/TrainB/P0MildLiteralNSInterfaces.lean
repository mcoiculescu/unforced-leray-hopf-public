import UnforcedLeray.Lib.TrainB.UniformDatumHeatMild
import UnforcedLeray.Lib.TrainB.P0UniformBallRestartSolenoidal

/-!
# Source-facing Navier–Stokes mild equations

The contraction leaves keep the affine map written as `seed + negativeMap`. These corollaries
expose the actual positive Gaussian heat-divergence response with its literal Navier–Stokes minus
sign for the uniform datum train and the arbitrary P₀-fixed restart interface.
-/

set_option autoImplicit false

noncomputable section

open Set

namespace UnforcedLeray.TrainB

open UnforcedLeray.HeatCylinder

/-- The period-uniform datum-seeded train with its mild equation displayed as seed minus the
positive projected Gaussian heat-divergence integral. All trace, P₀, component, and uniqueness
conclusions of the underlying uniform train are retained. -/
theorem exists_uniform_short_datumHeat_NS_mild_train {ν : ℝ} (hν : 0 < ν) :
    ∃ T : ℝ, ∃ hT : 0 < T,
      ∀ c : ℝ, (hc2 : 2 ≤ c) →
        ∃ u : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c),
          ‖u‖ ≤ 2 * (4 * datumUniformH3ComponentConstant) ∧
          u = (datumHeatSeedPath (by linarith : 0 < c) hν |>.comp compactTimeInclusion) +
            projectedNonlinearDuhamelCompactMap (by linarith : 0 < c)
              (by linarith : 1 ≤ c) hν hT.le u ∧
          (∀ t, u t = datumHeatSeedPath (by linarith : 0 < c) hν (t : ℝ) -
            projectedHeatNonlinearityIntegral (ν := ν) (by linarith : 0 < c)
              (by linarith : 1 ≤ c) (extendCompactPath hT.le u) (t : ℝ)) ∧
          (∀ t, P0H3CLM (by linarith : 0 < c) (u t) = u t) ∧
          vecH3CellDerivCLM Sob.Idx.zero (u (compactEvolutionZero hT)) =
            (memLp_datum_word_derivative (by linarith : 0 < c) Sob.Idx.zero).toLp
              (Train.datum c) ∧
          (∀ t α, vecH3CellDerivCLM α (u t) ∈ Cyl.divFree c) ∧
          (∀ t : Icc (0 : ℝ) T, ∀ α : Sob.Idx 2 3,
            ‖vecH3CellDerivCLM α (u t)‖ ≤ 2 * (4 * datumUniformH3ComponentConstant)) ∧
          (∀ v : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c),
            ‖v‖ ≤ 2 * (4 * datumUniformH3ComponentConstant) →
            v = (datumHeatSeedPath (by linarith : 0 < c) hν |>.comp compactTimeInclusion) +
              projectedNonlinearDuhamelCompactMap (by linarith : 0 < c)
                (by linarith : 1 ≤ c) hν hT.le v → v = u) := by
  obtain ⟨T, hT, hsource⟩ := exists_uniform_short_datumHeat_solenoidal_mild_train hν
  refine ⟨T, hT, fun c hc2 => ?_⟩
  have hc : 0 < c := by linarith
  have hc1 : 1 ≤ c := by linarith
  obtain ⟨u, hu, hfix, hP0, htrace, hdiv, hbound, huniq⟩ := hsource c hc2
  let g : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c) :=
    (datumHeatSeedPath hc hν).comp compactTimeInclusion
  refine ⟨u, hu, ?_, ?_, hP0, htrace, hdiv, hbound, ?_⟩
  · simpa [g, compactTimeInclusion] using hfix
  · intro t
    have hns := compact_mild_fixedPoint_eq_seed_sub_positiveDuhamel
      hc hc1 hν hT.le g u hfix t
    simpa [g, compactTimeInclusion] using hns
  · intro v hv hfv
    exact huniq v (by simpa using hv) (by simpa [g, compactTimeInclusion] using hfv)

/-- The period-fixed P₀-ball restart with its actual positive-response minus sign exposed, while
retaining the common-time, trace, all-component solenoidality, component bound, and uniqueness
conclusions. -/
theorem exists_uniform_short_projected_NS_mild_train_on_P0_ball_allComponentsDivFree
    {c ν M : ℝ} (hc : 0 < c) (hc1 : 1 ≤ c) (hν : 0 < ν) (hM : 0 ≤ M) :
    ∃ T : ℝ, ∃ hT : 0 < T,
      ∀ x : VectorH3 c, ‖x‖ ≤ M → P0H3CLM hc x = x →
        ∃ u : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c),
          ‖u‖ ≤ 2 * M ∧
          u = (projectedHeatSeedPath hc hν x).comp compactTimeInclusion +
            projectedNonlinearDuhamelCompactMap hc hc1 hν hT.le u ∧
          (∀ t, u t = (projectedHeatSeedPath hc hν x).comp compactTimeInclusion t -
            projectedHeatNonlinearityIntegral (ν := ν) hc hc1
              (extendCompactPath hT.le u) (t : ℝ)) ∧
          (∀ t, P0H3CLM hc (u t) = u t) ∧
          u (compactEvolutionZero hT) = x ∧
          (∀ t α, vecH3CellDerivCLM α (u t) ∈ Cyl.divFree c) ∧
          (∀ t : Icc (0 : ℝ) T, ∀ α : Sob.Idx 2 3,
            ‖vecH3CellDerivCLM α (u t)‖ ≤ 2 * M) ∧
          (∀ v : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c),
            ‖v‖ ≤ 2 * M →
            v = (projectedHeatSeedPath hc hν x).comp compactTimeInclusion +
              projectedNonlinearDuhamelCompactMap hc hc1 hν hT.le v → v = u) := by
  obtain ⟨T, hT, hsource⟩ :=
    exists_uniform_short_projected_mild_train_on_P0_ball_allComponentsDivFree hc hc1 hν hM
  refine ⟨T, hT, fun x hxnorm hxP0 => ?_⟩
  obtain ⟨u, hu, hfix, hP0, htrace, hdiv, hbound, huniq⟩ := hsource x hxnorm hxP0
  let g : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c) :=
    (projectedHeatSeedPath hc hν x).comp compactTimeInclusion
  refine ⟨u, hu, ?_, ?_, hP0, htrace, hdiv, hbound, ?_⟩
  · simpa [g] using hfix
  · intro t
    have hns := compact_mild_fixedPoint_eq_seed_sub_positiveDuhamel
      hc hc1 hν hT.le g u hfix t
    simpa [g] using hns
  · intro v hv hfv
    exact huniq v (by simpa using hv) (by simpa [g] using hfv)

#print axioms UnforcedLeray.TrainB.exists_uniform_short_datumHeat_NS_mild_train
#print axioms UnforcedLeray.TrainB.exists_uniform_short_projected_NS_mild_train_on_P0_ball_allComponentsDivFree

end UnforcedLeray.TrainB
