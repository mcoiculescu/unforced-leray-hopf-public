import UnforcedLeray.Units.B0146.LatticeSums

/-!
# B0146, helper: explicit Gaussian-vortex calculus at width `a`

Blueprint unit **B0146** (`eq:st18-t00144`, `paper/main.tex` lines 2196–2216).

The isolated heat vortex of width `a` is `V = vExp a = (u1 a, u2 a)` with
`u1 a w = -a⁻² w₂ e^{-|w|²/(4a)}`, `u2 a w = a⁻² w₁ e^{-|w|²/(4a)}` (unit B0113, `vExp`), and
its radial pressure is `pExp a = -a⁻³ e^{-|w|²/(2a)}`. This file lists the explicit first and
second Cartesian partial derivatives, the width derivatives, the pointwise identities
(divergence, heat equation, Euler balance in the form needed for the cross stress), and the
Gaussian decay of every function involved. The derivative computations are those of
`Units/B0113.lean` (`vExp1_x`, …, `vExp2_a`), restated as `HasDerivAt` along lines.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.B0146

open UnforcedLeray.GaussianVortex
open UnforcedLeray.B0113 (gw vExp pExp hasDerivAt_mul_gw_x hasDerivAt_mul_gw_y hasDerivAt_sq'
  hasDerivAt_gw_x hasDerivAt_gw_y vExp1_a vExp2_a)

/-! ### The explicit functions -/

/-- First component of `vExp a`. -/
def u1 (a : ℝ) (w : Plane) : ℝ := -(a⁻¹ ^ 2) * w.2 * gw a w
/-- Second component of `vExp a`. -/
def u2 (a : ℝ) (w : Plane) : ℝ := a⁻¹ ^ 2 * w.1 * gw a w
def u1x (a : ℝ) (w : Plane) : ℝ := a⁻¹ ^ 3 * w.1 * w.2 / 2 * gw a w
def u1y (a : ℝ) (w : Plane) : ℝ := a⁻¹ ^ 2 * (a⁻¹ * w.2 ^ 2 / 2 - 1) * gw a w
def u2x (a : ℝ) (w : Plane) : ℝ := a⁻¹ ^ 2 * (1 - a⁻¹ * w.1 ^ 2 / 2) * gw a w
def u2y (a : ℝ) (w : Plane) : ℝ := -(a⁻¹ ^ 3 * w.1 * w.2 / 2) * gw a w
def u1xx (a : ℝ) (w : Plane) : ℝ := a⁻¹ ^ 3 * w.2 / 2 * (1 - a⁻¹ * w.1 ^ 2 / 2) * gw a w
def u1yy (a : ℝ) (w : Plane) : ℝ := a⁻¹ ^ 3 * w.2 * (3 / 2 - a⁻¹ * w.2 ^ 2 / 4) * gw a w
def u2xx (a : ℝ) (w : Plane) : ℝ := -(a⁻¹ ^ 3 * w.1 * (3 / 2 - a⁻¹ * w.1 ^ 2 / 4)) * gw a w
def u2yy (a : ℝ) (w : Plane) : ℝ := -(a⁻¹ ^ 3 * w.1 / 2 * (1 - a⁻¹ * w.2 ^ 2 / 2)) * gw a w
/-- Width derivative of `u1`. -/
def u1a (a : ℝ) (w : Plane) : ℝ :=
  a⁻¹ ^ 2 * w.2 * (2 * a⁻¹ - a⁻¹ ^ 2 * radiusSq w / 4) * gw a w
/-- Width derivative of `u2`. -/
def u2a (a : ℝ) (w : Plane) : ℝ :=
  a⁻¹ ^ 2 * w.1 * (a⁻¹ ^ 2 * radiusSq w / 4 - 2 * a⁻¹) * gw a w
/-- `∂ₓ pExp`. -/
def prX (a : ℝ) (w : Plane) : ℝ := a⁻¹ ^ 4 * w.1 * (gw a w * gw a w)
/-- `∂_y pExp`. -/
def prY (a : ℝ) (w : Plane) : ℝ := a⁻¹ ^ 4 * w.2 * (gw a w * gw a w)

theorem vExp_eq (a : ℝ) (w : Plane) : vExp a w = (u1 a w, u2 a w) := rfl

/-! ### Derivatives along lines -/

theorem hx_u1 (a : ℝ) (w : Plane) : HasDerivAt (fun t => u1 a (t, w.2)) (u1x a w) w.1 :=
  (hasDerivAt_mul_gw_x a w (hasDerivAt_const w.1 (-(a⁻¹ ^ 2) * w.2))).congr_deriv
    (by unfold u1x; ring)

theorem hy_u1 (a : ℝ) (w : Plane) : HasDerivAt (fun t => u1 a (w.1, t)) (u1y a w) w.2 :=
  (hasDerivAt_mul_gw_y a w ((hasDerivAt_id' w.2).const_mul (-(a⁻¹ ^ 2)))).congr_deriv
    (by unfold u1y; ring)

theorem hx_u2 (a : ℝ) (w : Plane) : HasDerivAt (fun t => u2 a (t, w.2)) (u2x a w) w.1 :=
  (hasDerivAt_mul_gw_x a w ((hasDerivAt_id' w.1).const_mul (a⁻¹ ^ 2))).congr_deriv
    (by unfold u2x; ring)

theorem hy_u2 (a : ℝ) (w : Plane) : HasDerivAt (fun t => u2 a (w.1, t)) (u2y a w) w.2 :=
  (hasDerivAt_mul_gw_y a w (hasDerivAt_const w.2 (a⁻¹ ^ 2 * w.1))).congr_deriv
    (by unfold u2y; ring)

theorem hx_u1x (a : ℝ) (w : Plane) : HasDerivAt (fun t => u1x a (t, w.2)) (u1xx a w) w.1 :=
  (hasDerivAt_mul_gw_x a w ((((hasDerivAt_id' w.1).const_mul (a⁻¹ ^ 3)).mul_const
    w.2).div_const 2)).congr_deriv (by unfold u1xx; ring)

theorem hy_u1y (a : ℝ) (w : Plane) : HasDerivAt (fun t => u1y a (w.1, t)) (u1yy a w) w.2 :=
  (hasDerivAt_mul_gw_y a w (((((hasDerivAt_sq' w.2).const_mul a⁻¹).div_const 2).sub_const
    1).const_mul (a⁻¹ ^ 2))).congr_deriv (by unfold u1yy; ring)

theorem hx_u2x (a : ℝ) (w : Plane) : HasDerivAt (fun t => u2x a (t, w.2)) (u2xx a w) w.1 :=
  (hasDerivAt_mul_gw_x a w (((((hasDerivAt_sq' w.1).const_mul a⁻¹).div_const 2).const_sub
    1).const_mul (a⁻¹ ^ 2))).congr_deriv (by unfold u2xx; ring)

theorem hy_u2y (a : ℝ) (w : Plane) : HasDerivAt (fun t => u2y a (w.1, t)) (u2yy a w) w.2 :=
  (hasDerivAt_mul_gw_y a w ((((hasDerivAt_id' w.2).const_mul (a⁻¹ ^ 3 * w.1)).div_const
    2).fun_neg)).congr_deriv (by unfold u2yy; ring)

theorem hx_p (a : ℝ) (w : Plane) : HasDerivAt (fun t => pExp a (t, w.2)) (prX a w) w.1 :=
  (((hasDerivAt_gw_x a w).fun_mul (hasDerivAt_gw_x a w)).const_mul (-(a⁻¹ ^ 3))).congr_deriv
    (by simp only [Prod.mk.eta, prX]; ring)

theorem hy_p (a : ℝ) (w : Plane) : HasDerivAt (fun t => pExp a (w.1, t)) (prY a w) w.2 :=
  (((hasDerivAt_gw_y a w).fun_mul (hasDerivAt_gw_y a w)).const_mul (-(a⁻¹ ^ 3))).congr_deriv
    (by simp only [Prod.mk.eta, prY]; ring)

theorem ha_u1 {b : ℝ} (hb : b ≠ 0) (w : Plane) : HasDerivAt (fun b' => u1 b' w) (u1a b w) b :=
  vExp1_a hb w

theorem ha_u2 {b : ℝ} (hb : b ≠ 0) (w : Plane) : HasDerivAt (fun b' => u2 b' w) (u2a b w) b :=
  vExp2_a hb w

/-! ### Pointwise identities -/

/-- `div V = 0`. -/
theorem div_u (a : ℝ) (w : Plane) : u1x a w + u2y a w = 0 := by
  unfold u1x u2y; ring

/-- Heat equation, first component: `ΔV₁ = ∂ₐV₁`. -/
theorem lap_u1 (a : ℝ) (w : Plane) : u1xx a w + u1yy a w = u1a a w := by
  unfold u1xx u1yy u1a; simp only [radiusSq]; ring

/-- Heat equation, second component: `ΔV₂ = ∂ₐV₂`. -/
theorem lap_u2 (a : ℝ) (w : Plane) : u2xx a w + u2yy a w = u2a a w := by
  unfold u2xx u2yy u2a; simp only [radiusSq]; ring

/-- Euler balance, first component, in divergence form:
`∂₁P + ∂₁(V₁V₁) + ∂₂(V₂V₁) = 0`. -/
theorem euler_u1 (a : ℝ) (w : Plane) :
    prX a w + (u1x a w * u1 a w + u1 a w * u1x a w) +
      (u2y a w * u1 a w + u2 a w * u1y a w) = 0 := by
  unfold prX u1x u1 u2y u2 u1y; ring

/-- Euler balance, second component, in divergence form:
`∂₂P + ∂₁(V₁V₂) + ∂₂(V₂V₂) = 0`. -/
theorem euler_u2 (a : ℝ) (w : Plane) :
    prY a w + (u1x a w * u2 a w + u1 a w * u2x a w) +
      (u2y a w * u2 a w + u2 a w * u2y a w) = 0 := by
  unfold prY u1x u2 u1 u2x u2y; ring

/-! ### Gaussian decay, uniformly for widths in `[A₁, A₂] ⊂ (0, ∞)` -/

section Decay

variable {A₁ A₂ : ℝ}

theorem gf_u1 (hA : 0 < A₁) : GF A₁ A₂ u1 := by unfold u1; decay_tac
theorem gf_u2 (hA : 0 < A₁) : GF A₁ A₂ u2 := by unfold u2; decay_tac
theorem gf_u1x (hA : 0 < A₁) : GF A₁ A₂ u1x := by unfold u1x; decay_tac
theorem gf_u1y (hA : 0 < A₁) : GF A₁ A₂ u1y := by unfold u1y; decay_tac
theorem gf_u2x (hA : 0 < A₁) : GF A₁ A₂ u2x := by unfold u2x; decay_tac
theorem gf_u2y (hA : 0 < A₁) : GF A₁ A₂ u2y := by unfold u2y; decay_tac
theorem gf_u1xx (hA : 0 < A₁) : GF A₁ A₂ u1xx := by unfold u1xx; decay_tac
theorem gf_u1yy (hA : 0 < A₁) : GF A₁ A₂ u1yy := by unfold u1yy; decay_tac
theorem gf_u2xx (hA : 0 < A₁) : GF A₁ A₂ u2xx := by unfold u2xx; decay_tac
theorem gf_u2yy (hA : 0 < A₁) : GF A₁ A₂ u2yy := by unfold u2yy; decay_tac
theorem gf_u1a (hA : 0 < A₁) : GF A₁ A₂ u1a := by unfold u1a; decay_tac
theorem gf_u2a (hA : 0 < A₁) : GF A₁ A₂ u2a := by unfold u2a; decay_tac
theorem gf_p (hA : 0 < A₁) : GF A₁ A₂ pExp := by unfold pExp; decay_tac
theorem gf_prX (hA : 0 < A₁) : GF A₁ A₂ prX := by unfold prX; decay_tac
theorem gf_prY (hA : 0 < A₁) : GF A₁ A₂ prY := by unfold prY; decay_tac

theorem gf_mul {f g : ℝ → Plane → ℝ} (hf : GF A₁ A₂ f) (hg : GF A₁ A₂ g) :
    GF A₁ A₂ (fun a w => f a w * g a w) := by
  obtain ⟨K, β, hK, hβ, h⟩ := hf
  refine GF.mul_left (fun ε hε => ⟨K, fun a ha w => (h a ha w).trans ?_⟩) hg
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by
    nlinarith [mul_nonneg hβ.le (radiusSq_nonneg w), mul_nonneg hε.le (radiusSq_nonneg w)])) hK

end Decay

end UnforcedLeray.B0146
