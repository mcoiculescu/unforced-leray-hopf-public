import UnforcedLeray.Lib.HeatCylinder.HeatVecH3OrbitContinuity

/-!
# Continuity of the actual H³ heat orbit on all real ages

The orbit is continuous for positive ages, strongly continuous at age zero, and constant on
negative ages under the declared identity convention.
-/

set_option autoImplicit false

noncomputable section

open Filter Topology

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.Train (Vec)

/-- The actual centered H³ Gaussian family, extended by the identity at nonpositive ages,
has a continuous orbit on the full real age line. -/
theorem continuous_heatVecH3Semigroup_orbit {c : ℝ} (hc : 0 < c)
    (x : UnforcedLeray.Cyl.H ℝ Vec c 0 3) :
    Continuous (fun θ : ℝ => heatVecH3Semigroup (c := c) (θ := θ) hc x) := by
  rw [continuous_iff_continuousAt]
  intro θ
  by_cases hpos : 0 < θ
  · have hwithin : ContinuousWithinAt
        (fun t : ℝ => heatVecH3Semigroup (c := c) (θ := t) hc x) (Set.Ici 0) θ :=
      continuousOn_heatVecH3Semigroup_orbit hc x θ (le_of_lt hpos)
    exact hwithin.continuousAt (Ici_mem_nhds hpos)
  · by_cases hneg : θ < 0
    · have hconst :
          (fun t : ℝ => heatVecH3Semigroup (c := c) (θ := t) hc x) =ᶠ[𝓝 θ]
            (fun _ : ℝ => x) := by
        filter_upwards [eventually_lt_nhds hneg] with t ht
        simp [heatVecH3Semigroup, not_lt.mpr (le_of_lt ht)]
      exact (continuousAt_congr hconst).2 tendsto_const_nhds
    · have hle0 : θ ≤ 0 := le_of_not_gt hpos
      have hge0 : 0 ≤ θ := le_of_not_gt hneg
      have hzero : θ = 0 := le_antisymm hle0 hge0
      subst θ
      let f : ℝ → UnforcedLeray.Cyl.H ℝ Vec c 0 3 :=
        fun t => heatVecH3Semigroup (c := c) (θ := t) hc x
      have h0 : f 0 = x := by
        dsimp [f]
        rw [heatVecH3Semigroup_eq_id_of_nonpos hc (le_refl (0 : ℝ))]
        rfl
      have htend : Tendsto f (𝓝 0) (𝓝 x) := by
        simpa only [f] using tendsto_heatVecH3Semigroup_apply_zero hc x
      have hwithin : ContinuousWithinAt f Set.univ 0 := by
        change Tendsto f (𝓝[Set.univ] 0) (𝓝 (f 0))
        rw [nhdsWithin_univ, h0]
        exact htend
      exact (continuousWithinAt_univ f 0).1 hwithin

end UnforcedLeray.HeatCylinder

#print axioms UnforcedLeray.HeatCylinder.continuous_heatVecH3Semigroup_orbit
