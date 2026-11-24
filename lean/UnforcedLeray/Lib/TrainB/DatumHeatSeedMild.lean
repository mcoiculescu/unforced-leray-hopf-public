import UnforcedLeray.Lib.TrainB.P0ProjectedLinearSeedMild
import UnforcedLeray.Lib.TrainB.InitialDatumH3Class
import UnforcedLeray.Lib.HeatCylinder.HeatVecH3OrbitContinuity

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.TrainB

open UnforcedLeray.Train (Vec)

private theorem norm_heatVecH3Semigroup_le_one_local {c θ : ℝ} (hc : 0 < c) :
    ‖HeatCylinder.heatVecH3Semigroup (c := c) (θ := θ) hc‖ ≤ 1 := by
  by_cases hθ : 0 < θ
  · simpa [HeatCylinder.heatVecH3Semigroup, hθ] using
      HeatCylinder.norm_actualHeatVecH3CLM_le_one hc hθ
  · rw [HeatCylinder.heatVecH3Semigroup_eq_id_of_nonpos hc (le_of_not_gt hθ)]
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    simp

/-- The actual H³ Gaussian heat orbit, extended by the initial datum to negative times. -/
noncomputable def datumHeatSeedPath {c ν : ℝ} (hc : 0 < c) (hν : 0 < ν) :
    ContinuousMap ℝ (VectorH3 c) := by
  let x : VectorH3 c := datumVecH3 hc
  let age : ℝ → ℝ := fun t => max 0 (ν * t)
  have hage : Continuous age := by
    dsimp [age]
    fun_prop
  have hmaps : MapsTo age Set.univ (Set.Ici 0) := by
    intro t ht
    exact le_max_left 0 (ν * t)
  have hcontOn := (HeatCylinder.continuousOn_heatVecH3Semigroup_orbit hc x).comp
    hage.continuousOn hmaps
  refine ⟨fun t => HeatCylinder.heatVecH3Semigroup (c := c) (θ := age t) hc x,
    ?_⟩
  exact continuousOn_univ.mp hcontOn

theorem datumHeatSeedPath_norm_le {c ν : ℝ} (hc : 0 < c) (hν : 0 < ν)
    (t : ℝ) :
    ‖datumHeatSeedPath hc hν t‖ ≤ ‖datumVecH3 hc‖ := by
  change ‖HeatCylinder.heatVecH3Semigroup (c := c)
      (θ := max 0 (ν * t)) hc (datumVecH3 hc)‖ ≤ _
  calc
    ‖HeatCylinder.heatVecH3Semigroup (c := c) (θ := max 0 (ν * t)) hc
        (datumVecH3 hc)‖ ≤
      ‖HeatCylinder.heatVecH3Semigroup (c := c) (θ := max 0 (ν * t)) hc‖ *
        ‖datumVecH3 hc‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖datumVecH3 hc‖ :=
      mul_le_mul_of_nonneg_right
        (norm_heatVecH3Semigroup_le_one_local hc) (norm_nonneg _)
    _ = ‖datumVecH3 hc‖ := one_mul _

theorem datumHeatSeedPath_zero {c ν : ℝ} (hc : 0 < c) (hν : 0 < ν) :
    datumHeatSeedPath hc hν 0 = datumVecH3 hc := by
  change HeatCylinder.heatVecH3Semigroup (c := c) (θ := max 0 (ν * 0)) hc
      (datumVecH3 hc) = _
  rw [mul_zero, max_eq_left (show (0 : ℝ) ≥ 0 by norm_num)]
  rw [HeatCylinder.heatVecH3Semigroup_eq_id_of_nonpos hc (le_refl 0)]
  simp

/-- The actual datum heat path supplies the bounded linear seed required by the projected
short-time fixed-point theorem. The theorem keeps the selected solenoidal solution tied to the
actual datum rather than an arbitrary existence witness. -/
theorem exists_short_datumHeat_projected_mild_train {c ν : ℝ}
    (hc2 : 2 ≤ c) (hν : 0 < ν) :
    ∃ T : ℝ, ∃ hT : 0 < T,
      ∃ u : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c),
        ‖u‖ ≤ 2 * ‖datumVecH3 (by linarith : 0 < c)‖ ∧
        u = (fun t : Icc (0 : ℝ) T =>
            P0H3CLM (by linarith : 0 < c) (datumHeatSeedPath (by linarith : 0 < c) hν t)) +
          projectedNonlinearDuhamelCompactMap (by linarith : 0 < c)
            (by linarith : 1 ≤ c) hν hT.le u ∧
        (∀ t, P0H3CLM (by linarith : 0 < c) (u t) = u t) ∧
        vecH3CellDerivCLM Sob.Idx.zero
            (u (compactEvolutionZero hT)) =
          (memLp_datum_word_derivative (by linarith : 0 < c) Sob.Idx.zero).toLp
            (Train.datum c) ∧
        (∀ v : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c),
          ‖v‖ ≤ 2 * ‖datumVecH3 (by linarith : 0 < c)‖ →
          v = (fun t : Icc (0 : ℝ) T =>
              P0H3CLM (by linarith : 0 < c)
                (datumHeatSeedPath (by linarith : 0 < c) hν t)) +
            projectedNonlinearDuhamelCompactMap (by linarith : 0 < c)
              (by linarith : 1 ≤ c) hν hT.le v → v = u) := by
  let hc : 0 < c := by linarith
  have hc1 : 1 ≤ c := by linarith
  let x : VectorH3 c := datumVecH3 hc
  let R : ℝ := 2 * ‖x‖
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hbound : ∀ t, ‖datumHeatSeedPath hc hν t‖ ≤ R / 2 := by
    intro t
    have h := datumHeatSeedPath_norm_le hc hν t
    calc
      ‖datumHeatSeedPath hc hν t‖ ≤ ‖x‖ := by simpa [x] using h
      _ = R / 2 := by dsimp [R]; ring
  have hzero : datumHeatSeedPath hc hν 0 = datumVecH3 hc :=
    datumHeatSeedPath_zero hc hν
  obtain ⟨T, hT, u, hu, hfix, husol, htrace, huniq⟩ :=
    exists_short_projectedLinearSeed_mild_train hc hc1 hν hR
      (datumHeatSeedPath hc hν) hbound hzero
  refine ⟨T, hT, u, ?_, ?_, husol, htrace, ?_⟩
  · change ‖u‖ ≤ R
    simpa [R, x] using hu
  · simpa [R, x] using hfix
  · intro v hv hfv
    apply huniq v
    · change ‖v‖ ≤ R
      simpa [R, x] using hv
    · simpa [R, x] using hfv

#print axioms UnforcedLeray.TrainB.datumHeatSeedPath
#print axioms UnforcedLeray.TrainB.datumHeatSeedPath_norm_le
#print axioms UnforcedLeray.TrainB.datumHeatSeedPath_zero
#print axioms UnforcedLeray.TrainB.exists_short_datumHeat_projected_mild_train

end UnforcedLeray.TrainB
