import UnforcedLeray.Short.PartI.Sub.PartI_T02_1_4_4_1_7_1
import UnforcedLeray.Lib.HeatCylinder.HeatVecH3SemigroupContraction

/-!
# Part I, `PartI:T02/1/4/4/1/7/2`: `HeatDiffUniform5` from the `H^3` Duhamel identity

Source `the November 2 reference manuscript`, lines 261-288.

`PartI_T02_1_4_4_1_7_1`), contraction of the semigroup and density `cylSmoothDense5`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Cyl (Plane)

theorem heatQuot_continuous (ν c : ℝ) (hc : 0 < c) (h : ℝ) :
    Continuous (heatQuot ν c hc h) := by
  unfold heatQuot
  have hr : Continuous (fun w : Cyl.H ℝ Cyl.Vec2 c 0 5 =>
      (Sob.W.restrict (by norm_num : 3 ≤ 5) w : Cyl.H ℝ Cyl.Vec2 c 0 3)) :=
    (Sob.W.restrict (by norm_num : 3 ≤ 5)).continuous
  exact (((HeatCylinder.heatVecH3Semigroup (c := c) (θ := ν * h) hc).continuous.comp hr).sub
    hr).const_smul (h⁻¹)

theorem heatDiffUniform5_of (hD : HeatDuhamelSmooth5) : HeatDiffUniform5 := by
  intro ν c hν hc
  refine ⟨ν * ‖hLap c 3‖, fun y h hpos hle => ?_⟩
  have hsm : ∀ (T : Plane → Cyl.Vec2) (hT : Sob.IsCylSmooth c T),
      ‖heatQuot ν c hc h (smoothH5Field hc T hT)‖
        ≤ ν * ‖hLap c 3‖ * ‖smoothH5Field hc T hT‖ := by
    intro T hT
    set z := smoothH5Field hc T hT with hz
    have hint := hD ν c hν hc T hT h hpos
    have hb : ‖∫ s in (0:ℝ)..h, ν • HeatCylinder.heatVecH3Semigroup (c := c) (θ := ν * s) hc
        (hLap c 3 z)‖ ≤ (ν * ‖hLap c 3 z‖) * |h - 0| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro s _
      rw [norm_smul, Real.norm_of_nonneg hν.le]
      have hS : ‖HeatCylinder.heatVecH3Semigroup (c := c) (θ := ν * s) hc (hLap c 3 z)‖
          ≤ ‖hLap c 3 z‖ :=
        (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_of_le_one_left (norm_nonneg _)
            (HeatCylinder.norm_heatVecH3Semigroup_le_one (c := c) (θ := ν * s) hc))
      exact mul_le_mul_of_nonneg_left hS hν.le
    unfold heatQuot
    rw [norm_smul, norm_inv, Real.norm_of_nonneg hpos.le]
    rw [hint]
    have h2 : ‖hLap c 3 z‖ ≤ ‖hLap c 3‖ * ‖z‖ := ContinuousLinearMap.le_opNorm _ _
    rw [abs_of_pos (by linarith : (0:ℝ) < h - 0)] at hb
    calc h⁻¹ * ‖∫ s in (0:ℝ)..h, ν • HeatCylinder.heatVecH3Semigroup (c := c) (θ := ν * s) hc
            (hLap c 3 z)‖ ≤ h⁻¹ * ((ν * ‖hLap c 3 z‖) * (h - 0)) :=
          mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hpos.le)
      _ = ν * ‖hLap c 3 z‖ := by field_simp; ring
      _ ≤ ν * (‖hLap c 3‖ * ‖z‖) := mul_le_mul_of_nonneg_left h2 hν.le
      _ = ν * ‖hLap c 3‖ * ‖z‖ := by ring
  have hclosed : IsClosed {y : Cyl.H ℝ Cyl.Vec2 c 0 5 | ‖heatQuot ν c hc h y‖ ≤ ν * ‖hLap c 3‖ * ‖y‖} :=
    isClosed_le ((heatQuot_continuous ν c hc h).norm) (continuous_const.mul continuous_norm)
  have hsub : closure {z : Cyl.H ℝ Cyl.Vec2 c 0 5 | ∃ (T : Plane → Cyl.Vec2) (hT : Sob.IsCylSmooth c T),
      z = smoothH5Field hc T hT} ⊆ {y | ‖heatQuot ν c hc h y‖ ≤ ν * ‖hLap c 3‖ * ‖y‖} := by
    apply closure_minimal _ hclosed
    rintro z ⟨T, hT, rfl⟩
    exact hsm T hT
  have hy : y ∈ closure {z : Cyl.H ℝ Cyl.Vec2 c 0 5 | ∃ (T : Plane → Cyl.Vec2) (hT : Sob.IsCylSmooth c T),
      z = smoothH5Field hc T hT} := by
    rw [Metric.mem_closure_iff]
    intro δ hδ
    obtain ⟨T, hT, hd⟩ := cylSmoothDense5 c hc y δ hδ
    exact ⟨_, ⟨T, hT, rfl⟩, hd⟩
  exact hsub hy

end UnforcedLeray.Short.PartI
