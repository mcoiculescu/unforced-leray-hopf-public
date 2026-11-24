import UnforcedLeray.Lib.TrainB.DatumHeatMildComponentEnvelope
import UnforcedLeray.Lib.HeatCylinder.HeatVecH3SemigroupContraction

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open Set

namespace UnforcedLeray.TrainB

/-- The ordinary H³ Gaussian orbit of an arbitrary state, projected into the actual P₀ range
and held constant for negative times. -/
noncomputable def projectedHeatSeedPath {c ν : ℝ} (hc : 0 < c) (hν : 0 < ν)
    (x : VectorH3 c) : ContinuousMap ℝ (VectorH3 c) := by
  let age : ℝ → ℝ := fun t => max 0 (ν * t)
  have hage : Continuous age := by
    dsimp [age]
    fun_prop
  have hmaps : MapsTo age Set.univ (Set.Ici 0) := by
    intro t ht
    exact le_max_left 0 (ν * t)
  have hOrbit := (HeatCylinder.continuousOn_heatVecH3Semigroup_orbit hc x).comp
    hage.continuousOn hmaps
  let H : ContinuousMap ℝ (VectorH3 c) :=
    ⟨fun t => HeatCylinder.heatVecH3Semigroup (c := c) (θ := age t) hc x,
      continuousOn_univ.mp hOrbit⟩
  exact ⟨fun t => P0H3CLM hc (H t), (P0H3CLM hc).continuous.comp H.continuous⟩

theorem projectedHeatSeedPath_norm_le {c ν : ℝ} (hc : 0 < c) (hν : 0 < ν)
    (x : VectorH3 c) (t : ℝ) :
    ‖projectedHeatSeedPath hc hν x t‖ ≤ ‖x‖ := by
  change ‖P0H3CLM hc
    (HeatCylinder.heatVecH3Semigroup (c := c) (θ := max 0 (ν * t)) hc x)‖ ≤ ‖x‖
  exact (P0H3CLM_apply_norm_le hc _).trans (calc
    ‖HeatCylinder.heatVecH3Semigroup (c := c) (θ := max 0 (ν * t)) hc x‖ ≤
        ‖HeatCylinder.heatVecH3Semigroup (c := c) (θ := max 0 (ν * t)) hc‖ * ‖x‖ :=
          ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right
      (HeatCylinder.norm_heatVecH3Semigroup_le_one hc) (norm_nonneg _)
    _ = ‖x‖ := one_mul _)

theorem projectedHeatSeedPath_zero_of_P0_fixed {c ν : ℝ}
    (hc : 0 < c) (hν : 0 < ν) (x : VectorH3 c)
    (hx : P0H3CLM hc x = x) : projectedHeatSeedPath hc hν x 0 = x := by
  change P0H3CLM hc
      (HeatCylinder.heatVecH3Semigroup (c := c) (θ := max 0 (ν * 0)) hc x) = x
  rw [mul_zero, max_eq_left (show (0 : ℝ) ≥ 0 by norm_num),
    HeatCylinder.heatVecH3Semigroup_eq_id_of_nonpos hc (le_refl 0)]
  exact hx

/-- Every P₀-fixed H³ state starts a short, unique projected mild train from its own actual
ordinary Gaussian heat orbit. This restart theorem retains the state as the exact centered H³
trace; it does not assume the state is the special Train datum. -/
theorem exists_short_projected_mild_train_from_P0_state {c ν : ℝ}
    (hc : 0 < c) (hc1 : 1 ≤ c) (hν : 0 < ν) (x : VectorH3 c)
    (hx : P0H3CLM hc x = x) :
    ∃ T : ℝ, ∃ hT : 0 < T,
      ∃ u : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c),
        ‖u‖ ≤ 2 * ‖x‖ ∧
        u = (projectedHeatSeedPath hc hν x).comp compactTimeInclusion +
          projectedNonlinearDuhamelCompactMap hc hc1 hν hT.le u ∧
        (∀ t, P0H3CLM hc (u t) = u t) ∧
        u (compactEvolutionZero hT) = x ∧
        (∀ v : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c),
          ‖v‖ ≤ 2 * ‖x‖ →
          v = (projectedHeatSeedPath hc hν x).comp compactTimeInclusion +
            projectedNonlinearDuhamelCompactMap hc hc1 hν hT.le v → v = u) := by
  let R : ℝ := 2 * ‖x‖
  have hR : 0 ≤ R := by dsimp [R]; positivity
  obtain ⟨T, hT, hsmall⟩ := exists_train_short_contraction_time hν hR
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
      _ = R / 2 := by dsimp [R]; ring
  have hgsol : ∀ t, P0H3CLM hc (g t) = g t := by
    intro t
    change P0H3CLM hc
      (P0H3CLM hc (HeatCylinder.heatVecH3Semigroup (c := c)
        (θ := max 0 (ν * (t : ℝ))) hc x)) = _
    exact P0H3CLM_idem hc _
  have hgzero : g (compactEvolutionZero hT) = x := by
    change projectedHeatSeedPath hc hν x 0 = x
    exact projectedHeatSeedPath_zero_of_P0_fixed hc hν x hx
  obtain ⟨u, hu, hfix⟩ := exists_compact_actual_mild_fixedPoint
    hc hc1 hν hT hR hsmall g hg
  have husol := compactActualMildFixedPoint_solenoidal hc hc1 hν hT g u hfix hgsol
  have htrace := compactActualMildFixedPoint_initialTrace hc hc1 hν hT g u hfix
  refine ⟨T, hT, u, ?_, ?_, husol, ?_, ?_⟩
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

#print axioms UnforcedLeray.TrainB.projectedHeatSeedPath
#print axioms UnforcedLeray.TrainB.projectedHeatSeedPath_norm_le
#print axioms UnforcedLeray.TrainB.exists_short_projected_mild_train_from_P0_state

end UnforcedLeray.TrainB
