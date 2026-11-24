import UnforcedLeray.Lib.TrainB.DatumHeatP0Fixed
import UnforcedLeray.Lib.TrainB.DatumHeatH3OperatorBridge
import UnforcedLeray.Lib.TrainB.DatumHeatSeedMild
import UnforcedLeray.Lib.TrainB.P0SolenoidalSeedMild

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open Set

namespace UnforcedLeray.TrainB

open UnforcedLeray.HeatCylinder

/-- Every ordered derivative of the actual viscosity-scaled datum heat seed is weakly
solenoidal. At positive age this is the literal Gaussian derivative identity; at nonpositive age
the seed is the original Gaussian datum. -/
theorem datumHeatSeedPath_components_divFree {c ν : ℝ} (hc2 : 2 ≤ c) (hν : 0 < ν) :
    ∀ t α, vecH3CellDerivCLM α (datumHeatSeedPath (by linarith : 0 < c) hν t) ∈
      Cyl.divFree c := by
  intro t α
  let hc : 0 < c := by linarith
  let age : ℝ := max 0 (ν * t)
  change vecH3CellDerivCLM α
    (heatVecH3Semigroup (c := c) (θ := age) hc (datumVecH3 hc)) ∈ Cyl.divFree c
  by_cases hage : 0 < age
  · rw [heatVecH3Semigroup_apply_of_pos hc hage, actualHeatVecH3CLM_apply]
    have hident : datumHeatVecH3 hc2 hage =
        actualHeatVecH3 hc hage (datumVecH3 hc) := by
      simpa only [actualHeatVecH3CLM_apply] using
        datumHeatVecH3_eq_actualHeatVecH3 hc2 hage
    rw [← hident]
    exact datumHeatVecH3_components_divFree hc2 hage α
  · have hageZero : age = 0 := le_antisymm (le_of_not_gt hage) (le_max_left _ _)
    rw [hageZero, heatVecH3Semigroup_eq_id_of_nonpos hc (le_refl 0)]
    exact datumVecH3_components_divFree hc α

/-- The literal actual Gaussian H³ seed, which is already P₀-fixed at every age, yields a short
projected mild train. The nonlinear Duhamel map remains the actual P₀-projected Gaussian map. -/
theorem exists_short_datumHeat_solenoidal_mild_train {c ν : ℝ}
    (hc2 : 2 ≤ c) (hν : 0 < ν) :
    ∃ T : ℝ, ∃ hT : 0 < T,
      ∃ u : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c),
        ‖u‖ ≤ 2 * ‖datumVecH3 (by linarith : 0 < c)‖ ∧
        u = (datumHeatSeedPath (by linarith : 0 < c) hν |>.comp compactTimeInclusion) +
          projectedNonlinearDuhamelCompactMap (by linarith : 0 < c)
            (by linarith : 1 ≤ c) hν hT.le u ∧
        (∀ t, P0H3CLM (by linarith : 0 < c) (u t) = u t) ∧
        vecH3CellDerivCLM Sob.Idx.zero (u (compactEvolutionZero hT)) =
          (memLp_datum_word_derivative (by linarith : 0 < c) Sob.Idx.zero).toLp
            (Train.datum c) ∧
        (∀ v : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c),
          ‖v‖ ≤ 2 * ‖datumVecH3 (by linarith : 0 < c)‖ →
          v = (datumHeatSeedPath (by linarith : 0 < c) hν |>.comp compactTimeInclusion) +
            projectedNonlinearDuhamelCompactMap (by linarith : 0 < c)
              (by linarith : 1 ≤ c) hν hT.le v → v = u) := by
  let hc : 0 < c := by linarith
  have hc1 : 1 ≤ c := by linarith
  let H : ContinuousMap ℝ (VectorH3 c) := datumHeatSeedPath hc hν
  let R : ℝ := 2 * ‖datumVecH3 hc‖
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hbound : ∀ t, ‖H t‖ ≤ R / 2 := by
    intro t
    have ht := datumHeatSeedPath_norm_le hc hν t
    change ‖datumHeatSeedPath hc hν t‖ ≤ R / 2
    calc
      ‖datumHeatSeedPath hc hν t‖ ≤ ‖datumVecH3 hc‖ := ht
      _ = R / 2 := by dsimp [R]; ring
  have hzero : H 0 = datumVecH3 hc := by
    exact datumHeatSeedPath_zero hc hν
  obtain ⟨T, hT, u, hu, hfix, husol, htrace, huniq⟩ :=
    exists_short_solenoidalSeed_mild_train hc hc1 hν hR H hbound hzero
      (datumHeatSeedPath_components_divFree hc2 hν)
  refine ⟨T, hT, u, ?_, ?_, husol, htrace, ?_⟩
  · change ‖u‖ ≤ R
    simpa [R, hc] using hu
  · simpa [R, H, hc, compactTimeInclusion] using hfix
  · intro v hv hfv
    apply huniq v
    · simpa [R, hc] using hv
    · simpa [H, hc, compactTimeInclusion] using hfv

#print axioms UnforcedLeray.TrainB.datumHeatSeedPath_components_divFree
#print axioms UnforcedLeray.TrainB.exists_short_datumHeat_solenoidal_mild_train

end UnforcedLeray.TrainB
