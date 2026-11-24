import UnforcedLeray.Short.PartI.Sub.PartI_T02_1_4_4_1_7_1_1

/-!
# Part I, `PartI:T02/1/4/4/1/7/1/1/1`: reduction of the age derivative to the `H^3` generator

Source `the November 2 reference manuscript`, lines 261-288.

This file proves the conditional reduction `heatAgeDerivSmooth5_of_generator`: the `H^3`
age derivative `HeatAgeDerivSmooth5` follows from the right-hand generator limit at age zero
`HeatGeneratorAtZero5` (the difference quotient `h⁻¹ (S(h) z - z)` tends to `Δ z` in `H^3` as
`h → 0+`). The generator limit `HeatGeneratorAtZero5` is the open analytic input (a separate task).
-/

set_option autoImplicit false

set_option maxHeartbeats 800000

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Cyl (Plane)

/-- **Open leaf (generator at age zero in `H^3`).** For cylinder-smooth `T` and
`z = smoothH5Field T` (restricted to `H^3`), the difference quotient
`h⁻¹ (S(h) z - z)` tends to `hLap c 3 (smoothH5Field T)` in `H^3` as `h → 0+`. -/
def HeatGeneratorAtZero5 : Prop :=
  ∀ (c : ℝ) (hc : 0 < c) (T : Plane → Cyl.Vec2) (hT : Sob.IsCylSmooth c T),
    Tendsto (fun h : ℝ => h⁻¹ •
        (HeatCylinder.heatVecH3Semigroup (c := c) (θ := h) hc
            (Sob.W.restrict (by norm_num : 3 ≤ 5) (smoothH5Field hc T hT) : Cyl.H ℝ Cyl.Vec2 c 0 3)
          - (Sob.W.restrict (by norm_num : 3 ≤ 5) (smoothH5Field hc T hT) : Cyl.H ℝ Cyl.Vec2 c 0 3)))
      (𝓝[>] 0) (𝓝 (hLap c 3 (smoothH5Field hc T hT)))

/-- Reduction: the generator limit at zero gives the `H^3` age derivative at every positive age,
by the semigroup law `S(θ) S(d) = S(θ + d)` on nonnegative ages and joint continuity. -/
theorem heatAgeDerivSmooth5_of (hG : HeatGeneratorAtZero5) : HeatAgeDerivSmooth5 := by
  intro c hc T hT θ hθ
  have hq := hG c hc T hT
  have hj := HeatCylinder.continuous_heatVecH3Semigroup_joint (c := c) hc
  have hcomp : ∀ (α β : ℝ) (x : Cyl.H ℝ Cyl.Vec2 c 0 3), 0 ≤ α → 0 ≤ β →
      HeatCylinder.heatVecH3Semigroup (c := c) (θ := α) hc
        (HeatCylinder.heatVecH3Semigroup (c := c) (θ := β) hc x)
        = HeatCylinder.heatVecH3Semigroup (c := c) (θ := α + β) hc x := by
    intro α β x hα hβ
    rw [← ContinuousLinearMap.comp_apply, HeatCylinder.heatVecH3Semigroup_comp_of_nonneg hc hα hβ]
  set z : Cyl.H ℝ Cyl.Vec2 c 0 3 :=
    (Sob.W.restrict (by norm_num : 3 ≤ 5) (smoothH5Field hc T hT) : Cyl.H ℝ Cyl.Vec2 c 0 3) with hz
  set w : Cyl.H ℝ Cyl.Vec2 c 0 3 := hLap c 3 (smoothH5Field hc T hT) with hw
  clear_value z w
  -- the difference-quotient map on the slope side
  have hF : Tendsto (fun p : ℝ × Cyl.H ℝ Cyl.Vec2 c 0 3 =>
      HeatCylinder.heatVecH3Semigroup (c := c) (θ := p.1) hc p.2) (𝓝 (θ, w))
      (𝓝 (HeatCylinder.heatVecH3Semigroup (c := c) (θ := θ) hc w)) :=
    hj.tendsto (θ, w)
  have hm1 : Tendsto (fun s : ℝ => min s θ) (𝓝[≠] θ) (𝓝 θ) := by
    have hcm : Continuous (fun s : ℝ => min s θ) := continuous_id.min continuous_const
    have h : Tendsto (fun s : ℝ => min s θ) (𝓝 θ) (𝓝 θ) := by
      have h0 := hcm.tendsto θ
      simp only [min_self] at h0
      exact h0
    exact h.mono_left nhdsWithin_le_nhds
  have hm2 : Tendsto (fun s : ℝ => |s - θ|) (𝓝[≠] θ) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · have hca : Continuous (fun s : ℝ => |s - θ|) := (continuous_id.sub continuous_const).abs
      have h : Tendsto (fun s : ℝ => |s - θ|) (𝓝 θ) (𝓝 0) := by
        have h0 := hca.tendsto θ
        simp only [sub_self, abs_zero] at h0
        exact h0
      exact h.mono_left nhdsWithin_le_nhds
    · exact eventually_nhdsWithin_of_forall fun s hs =>
        abs_pos.mpr (sub_ne_zero.mpr hs)
  have hg : Tendsto (fun s : ℝ => (min s θ, |s - θ|⁻¹ •
      (HeatCylinder.heatVecH3Semigroup (c := c) (θ := |s - θ|) hc z - z)))
      (𝓝[≠] θ) (𝓝 (θ, w)) :=
    hm1.prodMk_nhds (hq.comp hm2)
  have hfin := hF.comp hg
  rw [hasDerivAt_iff_tendsto_slope]
  have hpos : ∀ᶠ s in 𝓝[≠] θ, (0:ℝ) < s := nhdsWithin_le_nhds (Ioi_mem_nhds hθ)
  refine hfin.congr' ?_
  filter_upwards [hpos, eventually_mem_nhdsWithin] with s hs0 hsne
  have hsne' : s ≠ θ := hsne
  rcases lt_or_gt_of_ne hsne' with hlt | hgt
  · have habs : |s - θ| = θ - s := by
      rw [abs_of_neg (by linarith)]
      ring
    have hA : HeatCylinder.heatVecH3Semigroup (c := c) (θ := s) hc
        (HeatCylinder.heatVecH3Semigroup (c := c) (θ := θ - s) hc z)
        = HeatCylinder.heatVecH3Semigroup (c := c) (θ := θ) hc z := by
      rw [hcomp s (θ - s) z hs0.le (by linarith)]
      congr 2
      ring
    simp only [Function.comp, min_eq_left hlt.le, habs, slope_def_module]
    rw [ContinuousLinearMap.map_smul, ContinuousLinearMap.map_sub, hA, show s - θ = -(θ - s) by ring, inv_neg]
    module
  · have habs : |s - θ| = s - θ := abs_of_pos (by linarith)
    have hA : HeatCylinder.heatVecH3Semigroup (c := c) (θ := θ) hc
        (HeatCylinder.heatVecH3Semigroup (c := c) (θ := s - θ) hc z)
        = HeatCylinder.heatVecH3Semigroup (c := c) (θ := s) hc z := by
      rw [hcomp θ (s - θ) z hθ.le (by linarith)]
      congr 2
      ring
    have hmin : min s θ = θ := min_eq_right hgt.le
    dsimp only [Function.comp_apply]
    rw [hmin, habs, slope_def_module, ContinuousLinearMap.map_smul, ContinuousLinearMap.map_sub, hA]

end UnforcedLeray.Short.PartI
