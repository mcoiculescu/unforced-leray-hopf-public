import UnforcedLeray.Short.PartI.Sub.PartI_T02_1_4_4_1_7_1

/-!
# Part I, `PartI:T02/1/4/4/1/7/1/1`: the `H^3` Duhamel identity from the age derivative

Source `the November 2 reference manuscript`, lines 261-288.


quantified over all real `ν`, but `heatVecH3Semigroup_eq_id_of_nonpos` makes `S(νh) = id` for
`ν < 0`, so the left side is `0` while the right side is `ν h Δz`.  Organizer oe1
(`PartI:T02/1/4/4/1/7/1/1/org`) added the viscosity hypothesis `0 < ν` there, so
`HeatDuhamelSmooth5Pos` below is now definitionally `HeatDuhamelSmooth5`
(`heatDuhamelSmooth5Pos_eq`).  Both are reduced to the analytic leaf `HeatAgeDerivSmooth5`
(`heatDuhamelSmooth5Pos_of`, `heatDuhamelSmooth5_of`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Cyl (Plane)

/-- **Leaf (age derivative in `H^3`; source lines 261-288).** For cylinder-smooth `T` and
`z = smoothH5Field T`, `θ ↦ S(θ) z` is differentiable in `H^3` at every `θ > 0` with derivative
`S(θ) (Δ z)` (age derivative of the Gaussian kernel,
`heatKernel2AgeDerivative_eq_spatialLaplacian`, `hasDerivAt_heatVecConvolution_age`). -/
def HeatAgeDerivSmooth5 : Prop :=
  ∀ (c : ℝ) (hc : 0 < c) (T : Plane → Cyl.Vec2) (hT : Sob.IsCylSmooth c T) (θ : ℝ), 0 < θ →
    HasDerivAt (fun s : ℝ => HeatCylinder.heatVecH3Semigroup (c := c) (θ := s) hc
        (Sob.W.restrict (by norm_num : 3 ≤ 5) (smoothH5Field hc T hT) : Cyl.H ℝ Cyl.Vec2 c 0 3))
      (HeatCylinder.heatVecH3Semigroup (c := c) (θ := θ) hc (hLap c 3 (smoothH5Field hc T hT))) θ

/-- The Duhamel identity of `HeatDuhamelSmooth5` for `0 < ν` (the only case used). -/
def HeatDuhamelSmooth5Pos : Prop :=
  ∀ (ν c : ℝ) (hν : 0 < ν) (hc : 0 < c) (T : Plane → Cyl.Vec2) (hT : Sob.IsCylSmooth c T)
    (h : ℝ), 0 < h →
    HeatCylinder.heatVecH3Semigroup (c := c) (θ := ν * h) hc
        (Sob.W.restrict (by norm_num : 3 ≤ 5) (smoothH5Field hc T hT) : Cyl.H ℝ Cyl.Vec2 c 0 3)
      - (Sob.W.restrict (by norm_num : 3 ≤ 5) (smoothH5Field hc T hT) : Cyl.H ℝ Cyl.Vec2 c 0 3)
    = ∫ s in (0:ℝ)..h, ν • HeatCylinder.heatVecH3Semigroup (c := c) (θ := ν * s) hc
        (hLap c 3 (smoothH5Field hc T hT))

theorem heatDuhamelSmooth5Pos_of (hA : HeatAgeDerivSmooth5) : HeatDuhamelSmooth5Pos := by
  intro ν c hν hc T hT h hh
  set x : Cyl.H ℝ Cyl.Vec2 c 0 3 :=
    (Sob.W.restrict (by norm_num : 3 ≤ 5) (smoothH5Field hc T hT) : Cyl.H ℝ Cyl.Vec2 c 0 3) with hx
  set w : Cyl.H ℝ Cyl.Vec2 c 0 3 := hLap c 3 (smoothH5Field hc T hT) with hw
  have hj := HeatCylinder.continuous_heatVecH3Semigroup_joint (c := c) hc
  have hF : Continuous (fun s : ℝ =>
      HeatCylinder.heatVecH3Semigroup (c := c) (θ := ν * s) hc x) := by
    have : Continuous (fun s : ℝ => (ν * s, x)) :=
      (continuous_const.mul continuous_id).prodMk continuous_const
    exact hj.comp this
  have hG : Continuous (fun s : ℝ =>
      ν • HeatCylinder.heatVecH3Semigroup (c := c) (θ := ν * s) hc w) := by
    have : Continuous (fun s : ℝ => (ν * s, w)) :=
      (continuous_const.mul continuous_id).prodMk continuous_const
    exact (hj.comp this).const_smul ν
  have hS0 : HeatCylinder.heatVecH3Semigroup (c := c) (θ := 0) hc x = x := by
    simp [HeatCylinder.heatVecH3Semigroup_eq_id_of_nonpos]
  have key := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le (le_of_lt hh)
    (f := fun s : ℝ => HeatCylinder.heatVecH3Semigroup (c := c) (θ := ν * s) hc x)
    (f' := fun s : ℝ => ν • HeatCylinder.heatVecH3Semigroup (c := c) (θ := ν * s) hc w)
    hF.continuousOn
    (by
      intro s hs
      have hs0 : 0 < s := hs.1
      have hd := hA c hc T hT (ν * s) (mul_pos hν hs0)
      have hm : HasDerivAt (fun s : ℝ => ν * s) ν s := by
        simpa using (hasDerivAt_id s).const_mul ν
      have := (HasDerivAt.scomp s hd hm)
      have h2 : HasDerivAt (fun s : ℝ =>
          HeatCylinder.heatVecH3Semigroup (c := c) (θ := ν * s) hc x)
          (ν • HeatCylinder.heatVecH3Semigroup (c := c) (θ := ν * s) hc w) s := this
      exact h2.hasDerivWithinAt)
    (hG.intervalIntegrable _ _)
  rw [key]
  simp only [mul_zero, hS0]

/-- `HeatDuhamelSmooth5Pos` is the corrected `HeatDuhamelSmooth5` (both carry `0 < ν`). -/
theorem heatDuhamelSmooth5Pos_eq : HeatDuhamelSmooth5Pos = HeatDuhamelSmooth5 := rfl

/-- The `H^3` Duhamel identity `HeatDuhamelSmooth5` (source lines 261-288) from the age
derivative leaf `HeatAgeDerivSmooth5`. -/
theorem heatDuhamelSmooth5_of (hA : HeatAgeDerivSmooth5) : HeatDuhamelSmooth5 :=
  heatDuhamelSmooth5Pos_of hA

end UnforcedLeray.Short.PartI

end
