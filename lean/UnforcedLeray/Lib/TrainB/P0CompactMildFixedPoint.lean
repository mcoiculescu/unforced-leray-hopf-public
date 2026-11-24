import UnforcedLeray.Lib.TrainB.P0CompactNonlinearBall

/-!
# Conditional local mild fixed point with the actual nonlinear Duhamel term

This is the Banach fixed-point step for an actual compact-time mild map once its linear heat orbit
is supplied. The seed path `g` is kept explicit, and its small norm is the exact condition needed
for the ball argument; no heat-orbit property is assumed inside the nonlinear estimate.
-/

set_option autoImplicit false

noncomputable section

open Set Metric

namespace UnforcedLeray.TrainB

/-- On a short interval, the affine Navier–Stokes mild map
`u ↦ g − positiveProjectedDuhamel(u)` has a fixed point in the H³ ball provided the actual linear
seed path lies in the half-radius ball. The internal contraction equation is written as `g + map`
where `map` is the negative actual Duhamel response. -/
theorem exists_compact_actual_mild_fixedPoint {c ν T R : ℝ}
    (hc : 0 < c) (hc1 : 1 ≤ c) (hν : 0 < ν) (hT : 0 < T) (hR : 0 ≤ R)
    (hsmall : projectedHeatNonlinearityLipschitzCoeff ν R * T ^ (1 / 2 : ℝ) ≤ 1 / 2)
    (g : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c)) (hg : ‖g‖ ≤ R / 2) :
    ∃ u : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c),
      ‖u‖ ≤ R ∧
      u = g + projectedNonlinearDuhamelCompactMap hc hc1 hν hT.le u := by
  let Φ : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c) →
      ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c) := fun u =>
    g + projectedNonlinearDuhamelCompactMap hc hc1 hν hT.le u
  let s : Set (ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c)) :=
    {u | ‖u‖ ≤ R}
  let K : NNReal := 1 / 2
  have hmap : MapsTo Φ s s := by
    intro u hu
    have huR : ‖u‖ ≤ R := hu
    change ‖Φ u‖ ≤ R
    have hduhamel := norm_projectedNonlinearDuhamelCompactMap_le_quarter
      hc hc1 hν hT hR hsmall u huR
    calc
      ‖Φ u‖ ≤ ‖g‖ + ‖projectedNonlinearDuhamelCompactMap hc hc1 hν hT.le u‖ :=
        norm_add_le _ _
      _ ≤ R / 2 + R / 4 := add_le_add hg hduhamel
      _ ≤ R := by linarith
  have hcontract : ContractingWith K (hmap.restrict Φ s s) := by
    refine ⟨?_, LipschitzWith.of_dist_le_mul fun u v => ?_⟩
    · apply NNReal.coe_lt_coe.mpr
      norm_num [K]
    · change dist (Φ u.val) (Φ v.val) ≤ (1 / 2 : ℝ) * dist u.val v.val
      have hdiff : Φ u.val - Φ v.val =
          projectedNonlinearDuhamelCompactMap hc hc1 hν hT.le u.val -
            projectedNonlinearDuhamelCompactMap hc hc1 hν hT.le v.val := by
        dsimp [Φ]
        abel
      rw [dist_eq_norm, hdiff, dist_eq_norm]
      exact norm_projectedNonlinearDuhamelCompactMap_sub_le_half hc hc1 hν hT hR
        hsmall u.val v.val u.property v.property
  have hclosed : IsClosed (s : Set (ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c))) :=
    isClosed_le continuous_norm continuous_const
  have hzero : (0 : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c)) ∈ s := by
    simp [s, hR]
  obtain ⟨u, hu, hfix, _, _⟩ := ContractingWith.exists_fixedPoint'
    hclosed.isComplete hmap hcontract hzero (edist_ne_top _ _)
  have huR : ‖u‖ ≤ R := by
    exact hu
  refine ⟨u, huR, ?_⟩
  simpa [Φ] using hfix.symm

/-- The compact fixed-point equation is literally the Navier–Stokes mild equation with a minus
sign in front of the positive projected Gaussian heat-divergence integral. -/
theorem compact_mild_fixedPoint_eq_seed_sub_positiveDuhamel {c ν T : ℝ}
    (hc : 0 < c) (hc1 : 1 ≤ c) (hν : 0 < ν) (hT : 0 ≤ T)
    (g u : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c))
    (hfix : u = g + projectedNonlinearDuhamelCompactMap hc hc1 hν hT u)
    (t : Icc (0 : ℝ) T) :
    u t = g t - projectedHeatNonlinearityIntegral (ν := ν) hc hc1
      (extendCompactPath hT u) t := by
  have hpoint := congrArg (fun f : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c) => f t) hfix
  change u t = g t + projectedNonlinearDuhamelCompactMap hc hc1 hν hT u t at hpoint
  rw [projectedNonlinearDuhamelCompactMap_apply] at hpoint
  simpa only [sub_eq_add_neg] using hpoint

/-- A short-interval fixed point with the literal minus-positive-Duhamel equation exposed. -/
theorem exists_compact_actual_NS_mild_fixedPoint {c ν T R : ℝ}
    (hc : 0 < c) (hc1 : 1 ≤ c) (hν : 0 < ν) (hT : 0 < T) (hR : 0 ≤ R)
    (hsmall : projectedHeatNonlinearityLipschitzCoeff ν R * T ^ (1 / 2 : ℝ) ≤ 1 / 2)
    (g : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c)) (hg : ‖g‖ ≤ R / 2) :
    ∃ u : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c),
      ‖u‖ ≤ R ∧
      u = g + projectedNonlinearDuhamelCompactMap hc hc1 hν hT.le u ∧
      ∀ t, u t = g t - projectedHeatNonlinearityIntegral (ν := ν) hc hc1
        (extendCompactPath hT.le u) t := by
  obtain ⟨u, hu, hfix⟩ :=
    exists_compact_actual_mild_fixedPoint hc hc1 hν hT hR hsmall g hg
  refine ⟨u, hu, hfix, ?_⟩
  intro t
  exact compact_mild_fixedPoint_eq_seed_sub_positiveDuhamel hc hc1 hν hT.le g u hfix t

/-- For each viscosity and radius, the explicit time choice gives a local fixed point for every
continuous linear seed path whose compact-time norm is at most half the radius. -/
theorem exists_short_interval_actual_mild_fixedPoint {c ν R : ℝ}
    (hc : 0 < c) (hc1 : 1 ≤ c) (hν : 0 < ν) (hR : 0 ≤ R) :
    ∃ T : ℝ, ∃ hT : 0 < T,
      ∀ g : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c),
        ‖g‖ ≤ R / 2 →
        ∃ u : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c),
          ‖u‖ ≤ R ∧
          u = g + projectedNonlinearDuhamelCompactMap hc hc1 hν (le_of_lt hT) u := by
  obtain ⟨T, hT, hsmall⟩ := exists_train_short_contraction_time hν hR
  refine ⟨T, hT, fun g hg => ?_⟩
  exact exists_compact_actual_mild_fixedPoint hc hc1 hν hT hR hsmall g hg

#print axioms UnforcedLeray.TrainB.exists_compact_actual_mild_fixedPoint
#print axioms UnforcedLeray.TrainB.compact_mild_fixedPoint_eq_seed_sub_positiveDuhamel
#print axioms UnforcedLeray.TrainB.exists_compact_actual_NS_mild_fixedPoint
#print axioms UnforcedLeray.TrainB.exists_short_interval_actual_mild_fixedPoint

end UnforcedLeray.TrainB
