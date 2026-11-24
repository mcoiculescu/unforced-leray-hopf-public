import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_2_2_1

/-!
# Calculus helpers for `PartIII-a:T21/2/2/2/1/2` (moving substitution)

Scaling and chain-rule lemmas for `pdCx`, used to differentiate `Φ(ζ,y) = a⁻¹ φ(r, √a y)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIIa.E0

open UnforcedLeray.Short.IIIa

/-- First derivative under a linear scaling `y ↦ c y`. -/
theorem pdCx_scale (f : ℝ × ℝ → ℂ) (hf : Differentiable ℝ f) (c : ℝ) (k : Fin 2) (y : ℝ × ℝ) :
    pdCx k (fun y => f (c * y.1, c * y.2)) y = (c : ℂ) * pdCx k f (c * y.1, c * y.2) := by
  unfold pdCx
  have h1 : HasFDerivAt (fun y : ℝ × ℝ => c • y) (c • ContinuousLinearMap.id ℝ (ℝ × ℝ)) y :=
    (hasFDerivAt_id y).const_smul c
  have h2 : HasFDerivAt (fun y : ℝ × ℝ => f (c • y))
      ((fderiv ℝ f (c • y)).comp (c • ContinuousLinearMap.id ℝ (ℝ × ℝ))) y :=
    (hf (c • y)).hasFDerivAt.comp y h1
  have h3 : fderiv ℝ (fun y : ℝ × ℝ => f (c * y.1, c * y.2)) y =
      (fderiv ℝ f (c • y)).comp (c • ContinuousLinearMap.id ℝ (ℝ × ℝ)) := h2.fderiv
  rw [h3]
  simp only [ContinuousLinearMap.comp_apply, smul_apply,
    ContinuousLinearMap.id_apply, map_smul, Complex.real_smul]
  rfl

/-- Constant complex factor. -/
theorem pdCx_const_mul (g : ℝ × ℝ → ℂ) (hg : Differentiable ℝ g) (K : ℂ) (k : Fin 2)
    (y : ℝ × ℝ) : pdCx k (fun y => K * g y) y = K * pdCx k g y := by
  unfold pdCx
  rw [((hg y).hasFDerivAt.const_mul K).fderiv]
  simp [smul_eq_mul]

/-- The first derivative of a smooth function is differentiable. -/
theorem pdCx_differentiable (f : ℝ × ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (k : Fin 2) :
    Differentiable ℝ (pdCx k f) := by
  unfold pdCx
  have h : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  have h2 : ContDiff ℝ ∞ (fun y => fderiv ℝ f y (B0579.dir k)) :=
    h.clm_apply contDiff_const
  exact h2.differentiable (by simp)

/-- The Laplacian under a linear scaling: `Δ[K f(c·)] = K c² (Δf)(c·)`. -/
theorem lapCx_scale (f : ℝ × ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (K : ℂ) (c : ℝ) (y : ℝ × ℝ) :
    lapCx (fun y => K * f (c * y.1, c * y.2)) y =
      K * (c : ℂ) ^ 2 * lapCx f (c * y.1, c * y.2) := by
  have hfd : Differentiable ℝ f := hf.differentiable (by simp)
  have hsc : Differentiable ℝ (fun y : ℝ × ℝ => f (c * y.1, c * y.2)) := by
    intro z
    have hl : DifferentiableAt ℝ (fun y : ℝ × ℝ => (c * y.1, c * y.2)) z := by fun_prop
    exact (hfd _).comp z hl
  have hd0 : Differentiable ℝ (pdCx 0 f) := pdCx_differentiable f hf 0
  have hd1 : Differentiable ℝ (pdCx 1 f) := pdCx_differentiable f hf 1
  have hdd00 : Differentiable ℝ (pdCx 0 (pdCx 0 f)) := pdCx_differentiable _ (by
    exact (hf.fderiv_right (by simp)).clm_apply contDiff_const) 0
  have hdd11 : Differentiable ℝ (pdCx 1 (pdCx 1 f)) := pdCx_differentiable _ (by
    exact (hf.fderiv_right (by simp)).clm_apply contDiff_const) 1
  have hg0 : Differentiable ℝ (fun y : ℝ × ℝ => pdCx 0 f (c * y.1, c * y.2)) := by
    intro z
    have hl : DifferentiableAt ℝ (fun y : ℝ × ℝ => (c * y.1, c * y.2)) z := by fun_prop
    exact (hd0 _).comp z hl
  have hg1 : Differentiable ℝ (fun y : ℝ × ℝ => pdCx 1 f (c * y.1, c * y.2)) := by
    intro z
    have hl : DifferentiableAt ℝ (fun y : ℝ × ℝ => (c * y.1, c * y.2)) z := by fun_prop
    exact (hd1 _).comp z hl
  have e0 : pdCx 0 (fun y => K * f (c * y.1, c * y.2)) =
      fun y => (K * c) * pdCx 0 f (c * y.1, c * y.2) := by
    funext z
    rw [pdCx_const_mul _ hsc K 0 z, pdCx_scale f hfd c 0 z]
    ring
  have e1 : pdCx 1 (fun y => K * f (c * y.1, c * y.2)) =
      fun y => (K * c) * pdCx 1 f (c * y.1, c * y.2) := by
    funext z
    rw [pdCx_const_mul _ hsc K 1 z, pdCx_scale f hfd c 1 z]
    ring
  have h00 : pdCx 0 (fun y => (K * c) * pdCx 0 f (c * y.1, c * y.2)) y =
      (K * c) * pdCx 0 (fun y => pdCx 0 f (c * y.1, c * y.2)) y :=
    pdCx_const_mul (fun y => pdCx 0 f (c * y.1, c * y.2)) hg0 (K * c) 0 y
  have h11 : pdCx 1 (fun y => (K * c) * pdCx 1 f (c * y.1, c * y.2)) y =
      (K * c) * pdCx 1 (fun y => pdCx 1 f (c * y.1, c * y.2)) y :=
    pdCx_const_mul (fun y => pdCx 1 f (c * y.1, c * y.2)) hg1 (K * c) 1 y
  have h00' : pdCx 0 (fun y => pdCx 0 f (c * y.1, c * y.2)) y =
      (c : ℂ) * pdCx 0 (pdCx 0 f) (c * y.1, c * y.2) :=
    pdCx_scale (pdCx 0 f) hd0 c 0 y
  have h11' : pdCx 1 (fun y => pdCx 1 f (c * y.1, c * y.2)) y =
      (c : ℂ) * pdCx 1 (pdCx 1 f) (c * y.1, c * y.2) :=
    pdCx_scale (pdCx 1 f) hd1 c 1 y
  have f00 : pdCx 0 (pdCx 0 (fun y => K * f (c * y.1, c * y.2))) y =
      K * (c : ℂ) ^ 2 * pdCx 0 (pdCx 0 f) (c * y.1, c * y.2) := by
    rw [e0, h00, h00']
    ring
  have f11 : pdCx 1 (pdCx 1 (fun y => K * f (c * y.1, c * y.2))) y =
      K * (c : ℂ) ^ 2 * pdCx 1 (pdCx 1 f) (c * y.1, c * y.2) := by
    rw [e1, h11, h11']
    ring
  unfold lapCx
  rw [f00, f11]
  ring

end UnforcedLeray.Short.IIIa.E0
