import UnforcedLeray.Short.PartI.Sub.PartI_T02_1_4_4_1_7_1_1_1_1

/-!
# Part I, `PartI:T02/1/4/4/1/7/1/1/1/1/1`: decomposition of `HeatTaylorUniform`

Source `the November 2 reference manuscript`, lines 261-288.  Three leaves:
* `HeatTaylorRemainder`: pointwise third-order Taylor bound with a uniform constant;
* `HeatGaussSplit`: the Gaussian average of the Taylor expansion (moments `1, 0, 2h Δ`);
* `HeatGaussCube`: the third absolute Gaussian moment is `O(h^{3/2})`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Cyl (Plane)

/-- Second-order Taylor remainder of `f` at `x` in the increment `w`:
`f(x-w) - f(x) + ∂_w f(x) - ½ ∂_w² f(x)`. -/
def heatTaylorR (f : Plane → Cyl.Vec2) (x w : Plane) : Cyl.Vec2 :=
  f (x - w) - f x + Sob.iterD [w] f x - (1 / 2 : ℝ) • Sob.iterD [w, w] f x

/-- **Leaf A (Taylor; source lines 261-288).** Cylinder-smooth `f` has all derivatives bounded
(periodic with compact transversal support), so `‖R(x,w)‖ ≤ M ‖w‖³` uniformly in `x`. -/
def HeatTaylorRemainder : Prop :=
  ∀ (c : ℝ) (_hc : 0 < c) (f : Plane → Cyl.Vec2) (_hf : Sob.IsCylSmooth c f),
    ∃ M : ℝ, ∀ x w : Plane, ‖heatTaylorR f x w‖ ≤ M * ‖w‖ ^ 3

/-- **Leaf B (Gaussian moments `∫K=1`, `∫K w=0`, `∫K w_i w_j=2hδ_ij`; lines 261-288).**
For `h > 0`: `K_h • R(x,·)` is integrable and
`heatVecConvolution h f x - f x - h Δ f x = ∫ K_h(w) R(x,w) dw`. -/
def HeatGaussSplit : Prop :=
  ∀ (c : ℝ) (_hc : 0 < c) (f : Plane → Cyl.Vec2) (_hf : Sob.IsCylSmooth c f)
    (h : ℝ) (_hh : 0 < h) (x : Plane),
    Integrable (fun w : Plane => B0284.heatKernel2 h w • heatTaylorR f x w) ∧
    HeatCylinder.heatVecConvolution h f x - f x
        - h • (Sob.iterD [((1:ℝ), (0:ℝ)), ((1:ℝ), (0:ℝ))] f x
            + Sob.iterD [((0:ℝ), (1:ℝ)), ((0:ℝ), (1:ℝ))] f x)
      = ∫ w : Plane, B0284.heatKernel2 h w • heatTaylorR f x w

/-- **Leaf C (third Gaussian moment; lines 261-288).**
`∫ K_h |w|³ = O(h^{3/2})` for `0 < h ≤ 1`, with `K_h |w|³` integrable. -/
def HeatGaussCube : Prop :=
  ∃ C : ℝ, ∀ h : ℝ, 0 < h → h ≤ 1 →
    Integrable (fun w : Plane => B0284.heatKernel2 h w * ‖w‖ ^ 3) ∧
    ∫ w : Plane, B0284.heatKernel2 h w * ‖w‖ ^ 3 ≤ C * h ^ (3 / 2 : ℝ)

theorem heatTaylorUniform_of (hA : HeatTaylorRemainder) (hB : HeatGaussSplit)
    (hC : HeatGaussCube) : HeatTaylorUniform := by
  intro c hc f hf
  obtain ⟨M, hM⟩ := hA c hc f hf
  obtain ⟨C, hC⟩ := hC
  refine ⟨M * C, fun h hh h1 x => ?_⟩
  obtain ⟨hint, hid⟩ := hB c hc f hf h hh x
  obtain ⟨hcint, hcb⟩ := hC h hh h1
  have hK : ∀ w : Plane, 0 ≤ B0284.heatKernel2 h w := fun w => B0284.heatKernel2_nonneg hh w
  have hrew : h⁻¹ • (HeatCylinder.heatVecConvolution h f x - f x)
      - (Sob.iterD [((1:ℝ), (0:ℝ)), ((1:ℝ), (0:ℝ))] f x
            + Sob.iterD [((0:ℝ), (1:ℝ)), ((0:ℝ), (1:ℝ))] f x)
      = h⁻¹ • ∫ w : Plane, B0284.heatKernel2 h w • heatTaylorR f x w := by
    rw [← hid]
    simp only [smul_sub, smul_smul, inv_mul_cancel₀ hh.ne', one_smul]
  rw [hrew, norm_smul, norm_inv, Real.norm_of_nonneg hh.le]
  have h1' : ‖∫ w : Plane, B0284.heatKernel2 h w • heatTaylorR f x w‖
      ≤ M * ∫ w : Plane, B0284.heatKernel2 h w * ‖w‖ ^ 3 := by
    calc _ ≤ ∫ w : Plane, ‖B0284.heatKernel2 h w • heatTaylorR f x w‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ w : Plane, M * (B0284.heatKernel2 h w * ‖w‖ ^ 3) := by
          refine integral_mono hint.norm (hcint.const_mul M) (fun w => ?_)
          rw [norm_smul, Real.norm_of_nonneg (hK w)]
          calc _ ≤ B0284.heatKernel2 h w * (M * ‖w‖ ^ 3) :=
                mul_le_mul_of_nonneg_left (hM x w) (hK w)
            _ = _ := by ring
      _ = _ := integral_const_mul _ _
  have hM0 : 0 ≤ M := by
    have := hM x (1, 0)
    have hn : ‖heatTaylorR f x (1, 0)‖ ≥ 0 := norm_nonneg _
    have h1n : ‖((1:ℝ), (0:ℝ))‖ = 1 := by simp
    rw [h1n] at this
    linarith
  have hsq : h⁻¹ * h ^ (3 / 2 : ℝ) = Real.sqrt h := by
    rw [Real.sqrt_eq_rpow, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
      Real.rpow_add hh, Real.rpow_one, ← mul_assoc, inv_mul_cancel₀ hh.ne', one_mul]
  calc h⁻¹ * ‖∫ w : Plane, B0284.heatKernel2 h w • heatTaylorR f x w‖
      ≤ h⁻¹ * (M * (C * h ^ (3 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_left (h1'.trans (mul_le_mul_of_nonneg_left hcb hM0))
          (inv_nonneg.mpr hh.le)
    _ = M * C * (h⁻¹ * h ^ (3 / 2 : ℝ)) := by ring
    _ = M * C * Real.sqrt h := by rw [hsq]

end UnforcedLeray.Short.PartI
