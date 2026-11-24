import UnforcedLeray.Lib.HeatCylinder.HeatVecH3ZeroAgeContinuity

/-!
# Strong continuity of the actual H³ heat orbit at every nonnegative age

The nonnegative semigroup law and contraction reduce every orbit increment to its age-zero
increment. This yields continuity on the full closed half-line.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory Filter Topology

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.Train (Vec)

private theorem heatVecH3Semigroup_norm_le_one {c θ : ℝ} (hc : 0 < c) :
    ‖heatVecH3Semigroup (c := c) (θ := θ) hc‖ ≤ 1 := by
  by_cases hθ : 0 < θ
  · simpa [heatVecH3Semigroup, hθ] using norm_actualHeatVecH3CLM_le_one hc hθ
  · simpa [heatVecH3Semigroup, hθ] using
      (ContinuousLinearMap.norm_id_le (𝕜 := ℝ)
        (E := UnforcedLeray.Cyl.H ℝ Vec c 0 3))

private theorem dist_heatVecH3Semigroup_orbit_le {c s t : ℝ} (hc : 0 < c)
    (hs : 0 ≤ s) (ht : 0 ≤ t) (x : UnforcedLeray.Cyl.H ℝ Vec c 0 3) :
    dist (heatVecH3Semigroup (c := c) (θ := t) hc x)
        (heatVecH3Semigroup (c := c) (θ := s) hc x) ≤
      dist (heatVecH3Semigroup (c := c) (θ := |t - s|) hc x) x := by
  by_cases hst : s ≤ t
  · let u : ℝ := t - s
    have hu : 0 ≤ u := sub_nonneg.mpr hst
    have htime : s + u = t := by dsimp [u]; ring
    let S : ℝ → UnforcedLeray.Cyl.H ℝ Vec c 0 3 →L[ℝ]
        UnforcedLeray.Cyl.H ℝ Vec c 0 3 := fun a =>
      heatVecH3Semigroup (c := c) (θ := a) hc
    have hcomp := heatVecH3Semigroup_comp_of_nonneg
      (c := c) (α := s) (β := u) hc hs hu
    change (S s).comp (S u) = S (s + u) at hcomp
    have hcomp' := congrArg (fun A : UnforcedLeray.Cyl.H ℝ Vec c 0 3 →L[ℝ]
        UnforcedLeray.Cyl.H ℝ Vec c 0 3 => A x) hcomp
    change S s (S u x) = S (s + u) x at hcomp'
    have hvalue : heatVecH3Semigroup (c := c) (θ := t) hc x =
        heatVecH3Semigroup (c := c) (θ := s) hc
          (heatVecH3Semigroup (c := c) (θ := u) hc x) := by
      simpa [S, htime] using hcomp'.symm
    have habs : |t - s| = u := by
      dsimp [u]
      exact abs_of_nonneg (sub_nonneg.mpr hst)
    rw [hvalue, habs]
    calc
      dist (heatVecH3Semigroup (c := c) (θ := s) hc
          (heatVecH3Semigroup (c := c) (θ := u) hc x))
          (heatVecH3Semigroup (c := c) (θ := s) hc x) ≤
        ‖heatVecH3Semigroup (c := c) (θ := s) hc‖ *
          dist (heatVecH3Semigroup (c := c) (θ := u) hc x) x :=
        (heatVecH3Semigroup (c := c) (θ := s) hc).dist_le_opNorm _ _
      _ ≤ 1 * dist (heatVecH3Semigroup (c := c) (θ := u) hc x) x :=
        mul_le_mul_of_nonneg_right (heatVecH3Semigroup_norm_le_one hc) dist_nonneg
      _ = _ := one_mul _
  · have hts : t ≤ s := le_of_not_ge hst
    let u : ℝ := s - t
    have hu : 0 ≤ u := sub_nonneg.mpr hts
    have htime : t + u = s := by dsimp [u]; ring
    let S : ℝ → UnforcedLeray.Cyl.H ℝ Vec c 0 3 →L[ℝ]
        UnforcedLeray.Cyl.H ℝ Vec c 0 3 := fun a =>
      heatVecH3Semigroup (c := c) (θ := a) hc
    have hcomp := heatVecH3Semigroup_comp_of_nonneg
      (c := c) (α := t) (β := u) hc ht hu
    change (S t).comp (S u) = S (t + u) at hcomp
    have hcomp' := congrArg (fun A : UnforcedLeray.Cyl.H ℝ Vec c 0 3 →L[ℝ]
        UnforcedLeray.Cyl.H ℝ Vec c 0 3 => A x) hcomp
    change S t (S u x) = S (t + u) x at hcomp'
    have hvalue : heatVecH3Semigroup (c := c) (θ := s) hc x =
        heatVecH3Semigroup (c := c) (θ := t) hc
          (heatVecH3Semigroup (c := c) (θ := u) hc x) := by
      simpa [S, htime] using hcomp'.symm
    have habs : |t - s| = u := by
      dsimp [u]
      rw [abs_of_nonpos (sub_nonpos.mpr hts)]
      ring
    rw [habs]
    rw [hvalue]
    calc
      dist (heatVecH3Semigroup (c := c) (θ := t) hc x)
          (heatVecH3Semigroup (c := c) (θ := t) hc
            (heatVecH3Semigroup (c := c) (θ := u) hc x)) ≤
        ‖heatVecH3Semigroup (c := c) (θ := t) hc‖ *
          dist x (heatVecH3Semigroup (c := c) (θ := u) hc x) :=
        (heatVecH3Semigroup (c := c) (θ := t) hc).dist_le_opNorm _ _
      _ ≤ 1 * dist x (heatVecH3Semigroup (c := c) (θ := u) hc x) :=
        mul_le_mul_of_nonneg_right (heatVecH3Semigroup_norm_le_one hc) dist_nonneg
      _ = _ := by rw [one_mul, dist_comm]
      _ = dist (heatVecH3Semigroup (c := c) (θ := u) hc x) x := rfl

/-- For each H³ datum, the actual Gaussian heat orbit is continuous on nonnegative ages. -/
theorem continuousOn_heatVecH3Semigroup_orbit {c : ℝ} (hc : 0 < c)
    (x : UnforcedLeray.Cyl.H ℝ Vec c 0 3) :
    ContinuousOn (fun θ : ℝ => heatVecH3Semigroup (c := c) (θ := θ) hc x)
      (Set.Ici 0) := by
  intro s hs
  change Tendsto (fun t : ℝ => heatVecH3Semigroup (c := c) (θ := t) hc x)
    (𝓝[Set.Ici 0] s) (𝓝 (heatVecH3Semigroup (c := c) (θ := s) hc x))
  apply tendsto_iff_dist_tendsto_zero.mpr
  have habs : Tendsto (fun t : ℝ => |t - s|) (𝓝[Set.Ici 0] s) (𝓝 0) := by
    have hcont : ContinuousAt (fun t : ℝ => |t - s|) s :=
      continuous_abs.continuousAt.comp (continuousAt_id.sub continuousAt_const)
    have h := hcont.tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[Set.Ici (0 : ℝ)] s ≤ 𝓝 s)
    simpa using h
  have hdelta : Tendsto
      (fun t : ℝ => dist (heatVecH3Semigroup (c := c) (θ := |t - s|) hc x) x)
      (𝓝[Set.Ici 0] s) (𝓝 0) :=
    (tendsto_iff_dist_tendsto_zero.mp (tendsto_heatVecH3Semigroup_apply_zero hc x)).comp habs
  have hupper : ∀ᶠ t in 𝓝[Set.Ici 0] s,
      dist (heatVecH3Semigroup (c := c) (θ := t) hc x)
          (heatVecH3Semigroup (c := c) (θ := s) hc x) ≤
        dist (heatVecH3Semigroup (c := c) (θ := |t - s|) hc x) x := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact dist_heatVecH3Semigroup_orbit_le hc hs ht x
  have hdist := tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ))
      (𝓝[Set.Ici 0] s) (𝓝 0)) hdelta
    (Filter.Eventually.of_forall fun _ => dist_nonneg) hupper
  simpa using hdist

end UnforcedLeray.HeatCylinder

#print axioms UnforcedLeray.HeatCylinder.dist_heatVecH3Semigroup_orbit_le
#print axioms UnforcedLeray.HeatCylinder.continuousOn_heatVecH3Semigroup_orbit
