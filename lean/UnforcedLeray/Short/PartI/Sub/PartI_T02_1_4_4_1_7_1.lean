import UnforcedLeray.Short.PartI.Sub.PartI_T02_1_4_4_1_7
import UnforcedLeray.Lib.HeatCylinder.HeatVecH3SemigroupJointContinuous
import UnforcedLeray.Lib.HeatCylinder.HeatVecH3ZeroAgeSmoothContinuity

/-!
# Part I, `PartI:T02/1/4/4/1/7/1`: `HeatSmoothGen5` from the `H^3` Duhamel identity

Source `the November 2 reference manuscript`, lines 261-288.

(`HeatDuhamelSmooth5`, `HeatLapSmoothIdentify5`) by the mean-value limit of a continuous
`H^3`-valued path.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Cyl (Plane)

/-- **Leaf D1** (Duhamel identity in `H^3`; source lines 261-288). For viscosity `0 < ν`, a
cylinder-smooth `T` and `z = smoothH5Field T`, `S(νh) z - z = ∫_0^h ν S(νs) (Δ z) ds` in `H^3`
(the hypothesis `0 < ν` is needed: `S(θ) = id` for `θ ≤ 0`; age derivative of the
Gaussian kernel: `heatKernel2AgeDerivative_eq_spatialLaplacian`
(`Lib/HeatCylinder/HeatKernelAgeLaplacian.lean:145`), `hasDerivAt_heatVecConvolution_age`
(`Lib/HeatCylinder/HeatVecAgeDerivative.lean:30`)). -/
def HeatDuhamelSmooth5 : Prop :=
  ∀ (ν c : ℝ) (hν : 0 < ν) (hc : 0 < c) (T : Plane → Cyl.Vec2) (hT : Sob.IsCylSmooth c T)
    (h : ℝ), 0 < h →
    HeatCylinder.heatVecH3Semigroup (c := c) (θ := ν * h) hc
        (Sob.W.restrict (by norm_num : 3 ≤ 5) (smoothH5Field hc T hT) : Cyl.H ℝ Cyl.Vec2 c 0 3)
      - (Sob.W.restrict (by norm_num : 3 ≤ 5) (smoothH5Field hc T hT) : Cyl.H ℝ Cyl.Vec2 c 0 3)
    = ∫ s in (0:ℝ)..h, ν • HeatCylinder.heatVecH3Semigroup (c := c) (θ := ν * s) hc
        (hLap c 3 (smoothH5Field hc T hT))

/-- **Leaf D2** (the Laplacian of a smooth field is the smooth field of the pointwise Laplacian;
source lines 261-288; see the `hLap` docstring in `Sub/T02_1_4_4_1.lean`). -/
def HeatLapSmoothIdentify5 : Prop :=
  ∀ (c : ℝ) (hc : 0 < c) (T : Plane → Cyl.Vec2) (hT : Sob.IsCylSmooth c T),
    ∃ hΔ : Sob.IsCylSmooth c (fun x => Sob.iterD [((1:ℝ), (0:ℝ)), ((1:ℝ), (0:ℝ))] T x + Sob.iterD [((0:ℝ), (1:ℝ)), ((0:ℝ), (1:ℝ))] T x),
      hLap c 3 (smoothH5Field hc T hT) =
        Sob.W.ofCylSmooth (ρ := Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ) (F := Cyl.Vec2) (k := 3) (p := 2)
          hc _ hΔ

theorem heatSmoothGen5_of (hD : HeatDuhamelSmooth5) (hI : HeatLapSmoothIdentify5) :
    HeatSmoothGen5 := by
  intro ν c hν hc T hT
  obtain ⟨hΔ, hEq⟩ := hI c hc T hT
  set z := smoothH5Field hc T hT with hz
  set w : Cyl.H ℝ Cyl.Vec2 c 0 3 := hLap c 3 z with hw
  have h0 : Tendsto (fun θ : ℝ => HeatCylinder.heatVecH3Semigroup (c := c) (θ := θ) hc w)
      (𝓝 0) (𝓝 w) := by
    have key := HeatCylinder.tendsto_heatVecH3Semigroup_apply_zero_ofCylSmooth hc hΔ
    rw [← hEq] at key
    exact key
  have hcont : Continuous (fun s : ℝ =>
      ν • HeatCylinder.heatVecH3Semigroup (c := c) (θ := ν * s) hc w) := by
    have hj := HeatCylinder.continuous_heatVecH3Semigroup_joint (c := c) hc
    have : Continuous (fun s : ℝ => (ν * s, w)) := (continuous_const.mul continuous_id).prodMk continuous_const
    exact (hj.comp this).const_smul ν
  have hS0 : HeatCylinder.heatVecH3Semigroup (c := c) (θ := 0) hc w = w := by
    have hc0 : Tendsto (fun θ : ℝ => HeatCylinder.heatVecH3Semigroup (c := c) (θ := θ) hc w)
        (𝓝 0) (𝓝 (HeatCylinder.heatVecH3Semigroup (c := c) (θ := 0) hc w)) :=
      (HeatCylinder.continuous_heatVecH3Semigroup_joint (c := c) hc |>.comp
        (continuous_id.prodMk continuous_const : Continuous fun θ : ℝ => (θ, w))).continuousAt
    exact tendsto_nhds_unique hc0 h0
  have hD' := (hcont.integral_hasStrictDerivAt 0 0).hasDerivAt
  have hsl := (hasDerivAt_iff_tendsto_slope.mp hD')
  have hsl2 := hsl
  simp only [mul_zero, hS0] at hsl2
  have hsl' := hsl2.mono_left (nhdsWithin_mono (0:ℝ) (fun x (hx : 0 < x) => (ne_of_gt hx : x ≠ 0)))
  refine hsl'.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh' : (0:ℝ) < h := hh
  have := hD ν c hν hc T hT h hh'
  rw [slope_def_module, heatQuot, intervalIntegral.integral_same, sub_zero, ← this]
  simp [hz, smoothH5Field]

end UnforcedLeray.Short.PartI
