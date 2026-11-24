import UnforcedLeray.Units.B0295.Kernel

/-!
# B0296: the gradient of the cylinder heat kernel and its `L¹` mass

Helper of unit B0296 (`unlabeled:5039`, tex lines 5033–5053, proof of
`lem:mixed-full-force-uniqueness`); blueprint unit B0296 of


The mild uniqueness argument uses the heat gradient smoothing
`‖e^{ντΔ} div‖_{L^p_sp → L^p_sp} ≤ C (ντ)^{-1/2}` (tex lines 5042–5046; blueprint
infrastructure INF05, scoping note `INF04-INF05-Heat.md` target T16). On the cylinder carrier of
B0284 (`heat θ` = convolution of the periodic lift with the planar Gaussian
`heatKernel2 θ w = G_θ(w.1) G_θ(w.2)`, `G_θ = B0191.heatKernel 1 θ`), `e^{θΔ} div` is the
convolution with the gradient of `heatKernel2 θ`. This file defines that gradient and computes
its `L¹` mass exactly:

* `dHeatKernel θ x = -(x/(2θ)) G_θ(x)` is the derivative of `G_θ` (`hasDerivAt_heatKernel`);
* `gradHeatKernel2 θ w = (∂_q, ∂_η) heatKernel2 θ w` (`hasDerivAt_heatKernel2_fst`,
  `hasDerivAt_heatKernel2_snd`);
* `∫ |G_θ'| = 2 (4πθ)^{-1/2}` (`integral_abs_dHeatKernel`), hence
  `∫ (|∂_q K_θ| + |∂_η K_θ|) = 4 (4πθ)^{-1/2} = 2 (πθ)^{-1/2}` (`lintegral_gradKernelAbs`).

This is the constant `C θ^{-1/2}` of the smoothing bound; the operator bound itself is in
`UnforcedLeray.Units.B0296.Conv`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Real Topology
open scoped NNReal ENNReal

namespace UnforcedLeray.B0296

open UnforcedLeray.B0284
open UnforcedLeray.GaussianVortex (Plane)

/-! ## The derivative of the one-dimensional kernel -/

/-- The derivative of the one-dimensional heat kernel `G_θ(x) = (4πθ)^{-1/2} e^{-x²/(4θ)}`:
`G_θ'(x) = -(x/(2θ)) G_θ(x)`. -/
def dHeatKernel (θ x : ℝ) : ℝ := -(x / (2 * θ)) * B0191.heatKernel 1 θ x

/-- `dHeatKernel θ` is the derivative of `G_θ = B0191.heatKernel 1 θ` (`θ ≠ 0`). -/
theorem hasDerivAt_heatKernel {θ : ℝ} (hθ : θ ≠ 0) (x : ℝ) :
    HasDerivAt (B0191.heatKernel 1 θ) (dHeatKernel θ x) x := by
  have h1 : HasDerivAt (fun y : ℝ => -y ^ 2 / (4 * 1 * θ)) (-(2 * x) / (4 * 1 * θ)) x := by
    have := ((hasDerivAt_pow 2 x).neg).div_const (4 * 1 * θ)
    simpa using this
  have h2 := h1.exp.const_mul (Real.sqrt (4 * Real.pi * 1 * θ))⁻¹
  have hfun : B0191.heatKernel 1 θ =
      fun y => (Real.sqrt (4 * Real.pi * 1 * θ))⁻¹ * Real.exp (-y ^ 2 / (4 * 1 * θ)) := by
    funext y
    rfl
  have hd : dHeatKernel θ x = (Real.sqrt (4 * Real.pi * 1 * θ))⁻¹ *
      (Real.exp (-x ^ 2 / (4 * 1 * θ)) * (-(2 * x) / (4 * 1 * θ))) := by
    unfold dHeatKernel B0191.heatKernel
    field_simp
    ring
  rw [hfun, hd]
  exact h2

theorem continuous_dHeatKernel (θ : ℝ) : Continuous (dHeatKernel θ) := by
  unfold dHeatKernel B0191.heatKernel
  fun_prop

theorem measurable_dHeatKernel (θ : ℝ) : Measurable (dHeatKernel θ) :=
  (continuous_dHeatKernel θ).measurable

theorem continuous_heatKernel1 (θ : ℝ) : Continuous (B0191.heatKernel 1 θ) := by
  unfold B0191.heatKernel
  fun_prop

/-! ## The gradient of the planar kernel -/

/-- The gradient `(∂_q K_θ, ∂_η K_θ)` of the planar heat kernel `K_θ = heatKernel2 θ`. -/
def gradHeatKernel2 (θ : ℝ) (w : Plane) : ℝ × ℝ :=
  (dHeatKernel θ w.1 * B0191.heatKernel 1 θ w.2, B0191.heatKernel 1 θ w.1 * dHeatKernel θ w.2)

/-- The first component of `gradHeatKernel2` is `∂_q heatKernel2`. -/
theorem hasDerivAt_heatKernel2_fst {θ : ℝ} (hθ : θ ≠ 0) (w : Plane) :
    HasDerivAt (fun x => heatKernel2 θ (x, w.2)) (gradHeatKernel2 θ w).1 w.1 := by
  show HasDerivAt (fun x => B0191.heatKernel 1 θ x * B0191.heatKernel 1 θ w.2)
    (dHeatKernel θ w.1 * B0191.heatKernel 1 θ w.2) w.1
  exact (hasDerivAt_heatKernel hθ w.1).mul_const _

/-- The second component of `gradHeatKernel2` is `∂_η heatKernel2`. -/
theorem hasDerivAt_heatKernel2_snd {θ : ℝ} (hθ : θ ≠ 0) (w : Plane) :
    HasDerivAt (fun y => heatKernel2 θ (w.1, y)) (gradHeatKernel2 θ w).2 w.2 := by
  show HasDerivAt (fun y => B0191.heatKernel 1 θ w.1 * B0191.heatKernel 1 θ y)
    (B0191.heatKernel 1 θ w.1 * dHeatKernel θ w.2) w.2
  exact (hasDerivAt_heatKernel hθ w.2).const_mul _

theorem measurable_gradHeatKernel2_fst (θ : ℝ) :
    Measurable fun w : Plane => (gradHeatKernel2 θ w).1 := by
  unfold gradHeatKernel2
  exact ((measurable_dHeatKernel θ).comp measurable_fst).mul
    ((continuous_heatKernel1 θ).measurable.comp measurable_snd)

theorem measurable_gradHeatKernel2_snd (θ : ℝ) :
    Measurable fun w : Plane => (gradHeatKernel2 θ w).2 := by
  unfold gradHeatKernel2
  exact ((continuous_heatKernel1 θ).measurable.comp measurable_fst).mul
    ((measurable_dHeatKernel θ).comp measurable_snd)

/-- The pointwise absolute gradient `|∂_q K_θ(w)| + |∂_η K_θ(w)|`, valued in `[0,∞)`. -/
def gradKernelAbs (θ : ℝ) (w : Plane) : ℝ≥0∞ :=
  ‖(gradHeatKernel2 θ w).1‖ₑ + ‖(gradHeatKernel2 θ w).2‖ₑ

theorem measurable_gradKernelAbs (θ : ℝ) : Measurable (gradKernelAbs θ) :=
  (measurable_gradHeatKernel2_fst θ).enorm.add (measurable_gradHeatKernel2_snd θ).enorm

theorem gradKernelAbs_ne_top (θ : ℝ) (w : Plane) : gradKernelAbs θ w ≠ ⊤ :=
  ENNReal.add_ne_top.2 ⟨enorm_ne_top, enorm_ne_top⟩

/-! ## The `L¹` masses -/

/-- `∫_{(0,∞)} x e^{-bx²} dx = (2b)⁻¹` (from Mathlib's complex form). -/
theorem integral_Ioi_mul_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) :
    ∫ x in Ioi (0 : ℝ), x * Real.exp (-b * x ^ 2) = (2 * b)⁻¹ := by
  have h := integral_mul_cexp_neg_mul_sq (b := (b : ℂ)) (by simpa using hb)
  have h2 : (∫ x in Ioi (0 : ℝ), ((x * Real.exp (-b * x ^ 2) : ℝ) : ℂ)) =
      (((2 * b)⁻¹ : ℝ) : ℂ) := by
    rw [show (((2 * b)⁻¹ : ℝ) : ℂ) = (2 * (b : ℂ))⁻¹ by push_cast; ring, ← h]
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    push_cast
    rfl
  rw [integral_complex_ofReal] at h2
  exact_mod_cast h2

/-- `∫_ℝ |x| e^{-bx²} dx = b⁻¹`. -/
theorem integral_abs_mul_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) :
    ∫ x : ℝ, |x| * Real.exp (-b * x ^ 2) = b⁻¹ := by
  have h := integral_comp_abs (f := fun x : ℝ => x * Real.exp (-b * x ^ 2))
  simp only [sq_abs] at h
  rw [h, integral_Ioi_mul_exp_neg_mul_sq hb]
  field_simp

/-- `|G_θ'(x)| = (2θ)⁻¹ (4πθ)^{-1/2} |x| e^{-x²/(4θ)}` (`θ > 0`). -/
theorem abs_dHeatKernel {θ : ℝ} (hθ : 0 < θ) (x : ℝ) :
    |dHeatKernel θ x| =
      ((2 * θ)⁻¹ * (Real.sqrt (4 * Real.pi * 1 * θ))⁻¹) *
        (|x| * Real.exp (-(4 * 1 * θ)⁻¹ * x ^ 2)) := by
  unfold dHeatKernel B0191.heatKernel
  have hs : 0 ≤ (Real.sqrt (4 * Real.pi * 1 * θ))⁻¹ := inv_nonneg.2 (Real.sqrt_nonneg _)
  rw [abs_mul, abs_mul, abs_neg, abs_div, abs_of_nonneg hs, abs_of_pos (by positivity : 0 < 2 * θ),
    abs_of_pos (Real.exp_pos _)]
  have he : -x ^ 2 / (4 * 1 * θ) = -(4 * 1 * θ)⁻¹ * x ^ 2 := by
    field_simp
  rw [he]
  field_simp

theorem integrable_dHeatKernel {θ : ℝ} (hθ : 0 < θ) : Integrable (dHeatKernel θ) := by
  have hb : 0 < (4 * 1 * θ)⁻¹ := by positivity
  have hi := ((integrable_mul_exp_neg_mul_sq hb).norm).const_mul
    ((2 * θ)⁻¹ * (Real.sqrt (4 * Real.pi * 1 * θ))⁻¹)
  refine Integrable.mono' hi (measurable_dHeatKernel θ).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_dHeatKernel hθ, Real.norm_eq_abs, abs_mul,
    abs_of_pos (Real.exp_pos _)]

/-- **The `L¹` mass of `G_θ'`**: `∫ |G_θ'| = 2 (4πθ)^{-1/2}` (`θ > 0`). -/
theorem integral_abs_dHeatKernel {θ : ℝ} (hθ : 0 < θ) :
    ∫ x, |dHeatKernel θ x| = 2 * (Real.sqrt (4 * Real.pi * 1 * θ))⁻¹ := by
  have hb : 0 < (4 * 1 * θ)⁻¹ := by positivity
  simp_rw [abs_dHeatKernel hθ]
  rw [integral_const_mul, integral_abs_mul_exp_neg_mul_sq hb, inv_inv]
  field_simp
  ring

theorem lintegral_enorm_dHeatKernel {θ : ℝ} (hθ : 0 < θ) :
    ∫⁻ x, ‖dHeatKernel θ x‖ₑ = ENNReal.ofReal (2 * (Real.sqrt (4 * Real.pi * 1 * θ))⁻¹) := by
  rw [← ofReal_integral_norm_eq_lintegral_enorm (integrable_dHeatKernel hθ)]
  simp_rw [Real.norm_eq_abs]
  rw [integral_abs_dHeatKernel hθ]

theorem integrable_heatKernel1 {θ : ℝ} (hθ : 0 < θ) : Integrable (B0191.heatKernel 1 θ) := by
  refine Integrable.of_integral_ne_zero ?_
  rw [integral_heatKernel_one hθ]
  exact one_ne_zero

theorem lintegral_enorm_heatKernel1 {θ : ℝ} (hθ : 0 < θ) :
    ∫⁻ x, ‖B0191.heatKernel 1 θ x‖ₑ = 1 := by
  rw [← ofReal_integral_norm_eq_lintegral_enorm (integrable_heatKernel1 hθ)]
  have : (fun x => ‖B0191.heatKernel 1 θ x‖) = B0191.heatKernel 1 θ := by
    funext x
    rw [Real.norm_eq_abs, abs_of_pos (B0191.heatKernel_pos one_pos hθ x)]
  rw [this, integral_heatKernel_one hθ, ENNReal.ofReal_one]

/-- **The `L¹` mass of the planar kernel gradient**:
`∫ (|∂_q K_θ| + |∂_η K_θ|) = 4 (4πθ)^{-1/2}` (`= 2 (πθ)^{-1/2}`), `θ > 0`. This is the
constant of the heat gradient smoothing `‖e^{θΔ} div‖_{L^p_sp → L^p_sp} ≤ C θ^{-1/2}`
(tex lines 5042–5046). -/
theorem lintegral_gradKernelAbs {θ : ℝ} (hθ : 0 < θ) :
    ∫⁻ w : Plane, gradKernelAbs θ w =
      ENNReal.ofReal (4 * (Real.sqrt (4 * Real.pi * 1 * θ))⁻¹) := by
  have hdm : Measurable fun x => ‖dHeatKernel θ x‖ₑ := (measurable_dHeatKernel θ).enorm
  have hgm : Measurable fun x => ‖B0191.heatKernel 1 θ x‖ₑ :=
    (continuous_heatKernel1 θ).measurable.enorm
  have h1 : ∫⁻ w : Plane, ‖(gradHeatKernel2 θ w).1‖ₑ =
      ENNReal.ofReal (2 * (Real.sqrt (4 * Real.pi * 1 * θ))⁻¹) := by
    have := lintegral_prod_mul (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
      hdm.aemeasurable hgm.aemeasurable
    rw [lintegral_enorm_dHeatKernel hθ, lintegral_enorm_heatKernel1 hθ, mul_one] at this
    rw [← this]
    refine lintegral_congr fun w => ?_
    simp only [gradHeatKernel2, enorm_mul]
  have h2 : ∫⁻ w : Plane, ‖(gradHeatKernel2 θ w).2‖ₑ =
      ENNReal.ofReal (2 * (Real.sqrt (4 * Real.pi * 1 * θ))⁻¹) := by
    have := lintegral_prod_mul (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
      hgm.aemeasurable hdm.aemeasurable
    rw [lintegral_enorm_dHeatKernel hθ, lintegral_enorm_heatKernel1 hθ, one_mul] at this
    rw [← this]
    refine lintegral_congr fun w => ?_
    simp only [gradHeatKernel2, enorm_mul]
  unfold gradKernelAbs
  rw [lintegral_add_left (measurable_gradHeatKernel2_fst θ).enorm, h1, h2,
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  ring

end UnforcedLeray.B0296
