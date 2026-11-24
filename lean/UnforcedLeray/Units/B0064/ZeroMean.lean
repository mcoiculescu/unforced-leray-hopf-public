import UnforcedLeray.Units.B0061

/-!
# B0064 helper: the integral of `A_E f` vanishes

Blueprint unit **B0064** (`paper/main.tex:1245`): "Integrals of both `D_E f` and `A_E f` vanish,
initially on smooth data and then by continuity or the group equation: [...] the second is
`div(E₀ Kf)` with integrable tails."

The library has no density theorem for test functions in `H^j_M` (see the note of unit B0063),
so the "smooth data, then continuity" step is replaced by a direct argument valid for every
integrable `f` (in particular every `f ∈ H^j_M`, `M > 1`, `B0008.HjM.integrable_value`):

* **Fubini.** `∫ (Kf)·∇E₀ dy = ∑_k ∫∫ K_k(y - z) ∂_kE₀(y) f(z) dz dy` is absolutely convergent
  (`integrable_prodFn`): `|K(w)| ≤ 1_{B₁}|K|(w) + (2π)^{-1}` and `∂_kE₀` is a bounded integrable
  (Schwartz) coefficient (`B0061.gradS`), so `∫ |K_k(y - z) ∂_kE₀(y)| dy ≤ C` uniformly in `z`.
  Hence `∫ A_E f = ∫ f(z) (∫ K(y - z)·∇E₀(y) dy) dz`.
* **Symmetry.** With `∇E₀(y) = k(|y|) y` (`B0009.gradE0_eq`),
  `K(y - z)·∇E₀(y) = -k(|y|) Im(z̄ y) / (2π|y - z|²)` (`symKernel_eq`), which is odd under the
  reflection of `ℂ` in the line `ℝz` (`refl`): it fixes `z`, `|y|`, `|y - z|` and changes the sign
  of `Im(z̄ y)`. Reflections preserve Lebesgue measure, so `∫ K(y - z)·∇E₀(y) dy = 0`
  (`integral_symKernel`).

This is the identity `∫ div(E₀ Kf) = 0` of the manuscript (`div Kf = 0`, so
`(Kf)·∇E₀ = div(E₀ Kf)`), proved by the antisymmetry of the kernel against radial gradients
instead of the divergence theorem with decaying tails.

Main declarations: `integral_perturbation_eq_zero` (`∫ A_E f = 0` for integrable `f`),
`integral_symKernel`, `integrable_prodFn`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ComplexConjugate

namespace UnforcedLeray.B0064

open UnforcedLeray.B0009 UnforcedLeray.B0061

/-! ### The near part of the kernel and the coefficient bounds -/

/-- The near part `1_{B₁} K_k` of the Biot–Savart kernel. -/
def kNear (k : Fin 2) : ℂ → ℂ := (ball (0 : ℂ) 1).indicator (kernel k)

theorem integrable_kNear (k : Fin 2) : Integrable (kNear k) volume :=
  (integrableOn_kernel_ball k).integrable_indicator measurableSet_ball

theorem norm_kernel_le_kNear (k : Fin 2) (w : ℂ) :
    ‖kernel k w‖ ≤ ‖kNear k w‖ + (2 * Real.pi)⁻¹ := by
  have hc : (0 : ℝ) ≤ (2 * Real.pi)⁻¹ := by positivity
  by_cases hw : w ∈ ball (0 : ℂ) 1
  · rw [kNear, indicator_of_mem hw]
    linarith
  · rw [kNear, indicator_of_notMem hw, norm_zero, zero_add]
    exact norm_kernel_le_of_notMem_ball k hw

/-- A uniform bound for the Schwartz coefficient `∂_k E₀` (`B0061.gradS`). -/
def gradBound (k : Fin 2) : ℝ := SchwartzMap.seminorm ℝ 0 0 (gradS k)

theorem norm_gradS_le (k : Fin 2) (y : ℂ) : ‖gradS k y‖ ≤ gradBound k :=
  SchwartzMap.norm_le_seminorm ℝ (gradS k) y

/-- The dominating function `y ↦ sup|∂_kE₀| · |1_{B₁}K_k(y - z)| + (2π)^{-1} |∂_kE₀(y)|` of
`y ↦ K_k(y - z) ∂_kE₀(y)`. -/
def domFn (k : Fin 2) (z y : ℂ) : ℝ :=
  gradBound k * ‖kNear k (y - z)‖ + (2 * Real.pi)⁻¹ * ‖gradS k y‖

theorem integrable_domFn (k : Fin 2) (z : ℂ) : Integrable (domFn k z) volume :=
  (((integrable_kNear k).comp_sub_right z).norm.const_mul _).add
    ((gradS k).integrable.norm.const_mul _)

/-- The `z`-independent bound `∫ domFn k z`. -/
def domConst (k : Fin 2) : ℝ :=
  gradBound k * (∫ w, ‖kNear k w‖) + (2 * Real.pi)⁻¹ * ∫ y, ‖gradS k y‖

theorem integral_domFn (k : Fin 2) (z : ℂ) : ∫ y, domFn k z y = domConst k := by
  unfold domFn domConst
  rw [integral_add (((integrable_kNear k).comp_sub_right z).norm.const_mul _)
      ((gradS k).integrable.norm.const_mul _), integral_const_mul, integral_const_mul,
    integral_sub_right_eq_self (μ := (volume : Measure ℂ)) (fun w => ‖kNear k w‖) z]

theorem norm_kernel_mul_gradS_le (k : Fin 2) (z y : ℂ) :
    ‖kernel k (y - z) * gradS k y‖ ≤ domFn k z y := by
  rw [norm_mul, domFn]
  have h1 := norm_kernel_le_kNear k (y - z)
  have h2 := norm_gradS_le k y
  have h3 : 0 ≤ ‖kNear k (y - z)‖ := norm_nonneg _
  have h4 : 0 ≤ ‖gradS k y‖ := norm_nonneg _
  calc ‖kernel k (y - z)‖ * ‖gradS k y‖
      ≤ (‖kNear k (y - z)‖ + (2 * Real.pi)⁻¹) * ‖gradS k y‖ :=
        mul_le_mul_of_nonneg_right h1 h4
    _ = ‖kNear k (y - z)‖ * ‖gradS k y‖ + (2 * Real.pi)⁻¹ * ‖gradS k y‖ := by ring
    _ ≤ ‖kNear k (y - z)‖ * gradBound k + (2 * Real.pi)⁻¹ * ‖gradS k y‖ := by gcongr
    _ = gradBound k * ‖kNear k (y - z)‖ + (2 * Real.pi)⁻¹ * ‖gradS k y‖ := by ring

/-- `y ↦ K_k(y - z) ∂_kE₀(y)` is integrable for every `z`. -/
theorem integrable_kernel_mul_gradS (k : Fin 2) (z : ℂ) :
    Integrable (fun y => kernel k (y - z) * gradS k y) volume :=
  (integrable_domFn k z).mono'
    (((measurable_kernel k).comp (measurable_id.sub_const z)).aestronglyMeasurable.mul
      (gradS k).continuous.aestronglyMeasurable)
    (ae_of_all _ (norm_kernel_mul_gradS_le k z))

/-- `∫ |K_k(y - z) ∂_kE₀(y)| dy ≤ C_k`, uniformly in `z`. -/
theorem integral_norm_kernel_mul_gradS_le (k : Fin 2) (z : ℂ) :
    ∫ y, ‖kernel k (y - z) * gradS k y‖ ≤ domConst k := by
  rw [← integral_domFn k z]
  exact integral_mono (integrable_kernel_mul_gradS k z).norm (integrable_domFn k z)
    (norm_kernel_mul_gradS_le k z)

/-! ### Fubini -/

/-- The integrand `(z, y) ↦ K_k(y - z) ∂_kE₀(y) f(z)` of `∫ ∂_kE₀ (Kf)_k`. -/
def prodFn (k : Fin 2) (f : ℂ → ℂ) (p : ℂ × ℂ) : ℂ :=
  kernel k (p.2 - p.1) * gradS k p.2 * f p.1

/-- **Absolute convergence of the double integral** for integrable `f`. -/
theorem integrable_prodFn (k : Fin 2) {f : ℂ → ℂ} (hf : Integrable f volume) :
    Integrable (prodFn k f) (volume.prod volume) := by
  have hmeas : AEStronglyMeasurable (prodFn k f) (volume.prod volume) :=
    ((((measurable_kernel k).comp (measurable_snd.sub measurable_fst)).aestronglyMeasurable).mul
      ((gradS k).continuous.comp continuous_snd).aestronglyMeasurable).mul
      hf.aestronglyMeasurable.comp_fst
  rw [integrable_prod_iff hmeas]
  refine ⟨ae_of_all _ fun z => (integrable_kernel_mul_gradS k z).mul_const (f z), ?_⟩
  refine (hf.norm.const_mul (domConst k)).mono' hmeas.norm.integral_prod_right'
    (ae_of_all _ fun z => ?_)
  have e : (∫ y, ‖prodFn k f (z, y)‖) = (∫ y, ‖kernel k (y - z) * gradS k y‖) * ‖f z‖ := by
    rw [← integral_mul_const]
    congr 1
    funext y
    simp only [prodFn, norm_mul]
  rw [e, Real.norm_of_nonneg (mul_nonneg (integral_nonneg fun _ => norm_nonneg _)
    (norm_nonneg _))]
  exact mul_le_mul_of_nonneg_right (integral_norm_kernel_mul_gradS_le k z) (norm_nonneg _)

/-! ### The symmetry of `K(y - z)·∇E₀(y)` -/

/-- `K(y - z)·∇E₀(y) = ∑_k K_k(y - z) ∂_kE₀(y)`. -/
def symKernel (z y : ℂ) : ℂ := ∑ k : Fin 2, kernel k (y - z) * gradS k y

/-- `K(y - z)·∇E₀(y) = -k(|y|) Im(z̄ y) / (2π|y - z|²)`, with `∇E₀(y) = k(|y|) y`. -/
theorem symKernel_eq (z y : ℂ) :
    symKernel z y = ((-(GaussianVortex.radialK ‖y‖ * (conj z * y).im) /
      (2 * Real.pi * ‖y - z‖ ^ 2) : ℝ) : ℂ) := by
  simp only [symKernel, Fin.sum_univ_two, kernel, gradS_zero, gradS_one, gradE0_eq]
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_add]
  congr 1
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div]
  congr 1
  simp only [perpComp, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.sub_re,
    Complex.sub_im]
  ring

theorem conj_ne_zero {z : ℂ} (hz : z ≠ 0) : conj z ≠ 0 := by
  rwa [ne_eq, map_eq_zero]

/-- **The reflection of `ℂ` in the line `ℝz`**, `y ↦ (z / z̄) ȳ`, a linear isometry. -/
def refl (z : ℂ) (hz : z ≠ 0) : ℂ ≃ₗᵢ[ℝ] ℂ :=
  Complex.conjLIE.trans (rotation (Circle.ofConjDivSelf (conj z) (conj_ne_zero hz)))

theorem refl_apply (z : ℂ) (hz : z ≠ 0) (y : ℂ) : refl z hz y = z / conj z * conj y := by
  simp only [refl, LinearIsometryEquiv.trans_apply, Complex.conjLIE_apply, rotation_apply]
  change conj (conj z) / conj z * conj y = _
  rw [Complex.conj_conj]

theorem refl_self (z : ℂ) (hz : z ≠ 0) : refl z hz z = z := by
  rw [refl_apply, div_mul_cancel₀ _ (conj_ne_zero hz)]

theorem im_conj_mul_refl (z : ℂ) (hz : z ≠ 0) (y : ℂ) :
    (conj z * refl z hz y).im = -(conj z * y).im := by
  have e : conj z * refl z hz y = conj (conj z * y) := by
    rw [refl_apply, map_mul, Complex.conj_conj]
    field_simp [conj_ne_zero hz]
  rw [e, Complex.conj_im]

theorem norm_refl_sub (z : ℂ) (hz : z ≠ 0) (y : ℂ) : ‖refl z hz y - z‖ = ‖y - z‖ := by
  have e : refl z hz y - z = refl z hz (y - z) := by rw [map_sub, refl_self]
  rw [e, LinearIsometryEquiv.norm_map]

/-- `K(y - z)·∇E₀(y)` is odd under the reflection in `ℝz`. -/
theorem symKernel_refl (z : ℂ) (hz : z ≠ 0) (y : ℂ) :
    symKernel z (refl z hz y) = -symKernel z y := by
  rw [symKernel_eq, symKernel_eq, LinearIsometryEquiv.norm_map, norm_refl_sub,
    im_conj_mul_refl, ← Complex.ofReal_neg]
  congr 1
  ring

/-- **`∫ K(y - z)·∇E₀(y) dy = 0`** for every `z ∈ ℂ`. -/
theorem integral_symKernel (z : ℂ) : ∫ y, symKernel z y = 0 := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp [symKernel_eq]
  · have h := MeasureTheory.integral_comp (refl z hz) (symKernel z)
    simp_rw [symKernel_refl z hz] at h
    rw [integral_neg] at h
    linear_combination (-(1 : ℂ) / 2) * h

/-! ### `∫ A_E f = 0` -/

/-- **`∫ (Kf)·∇E₀ = 0`** for every integrable `f` (`paper/main.tex:1245`, unit B0064): the
integral of `A_E f = perturbation f` vanishes. -/
theorem integral_perturbation_eq_zero {f : ℂ → ℂ} (hf : Integrable f volume) :
    ∫ y, perturbation f y = 0 := by
  have hint : ∀ k : Fin 2, Integrable (prodFn k f) (volume.prod volume) := fun k =>
    integrable_prodFn k hf
  have h1 : ∀ (k : Fin 2) (y : ℂ), gradS k y * biotSavart f k y = ∫ z, prodFn k f (z, y) := by
    intro k y
    rw [biotSavart_apply, ← integral_const_mul]
    congr 1
    funext z
    simp only [prodFn]
    ring
  have h2 : ∀ (k : Fin 2) (z : ℂ),
      ∫ y, prodFn k f (z, y) = (∫ y, kernel k (y - z) * gradS k y) * f z := by
    intro k z
    rw [← integral_mul_const]
    rfl
  have hpert : (fun y => perturbation f y) = fun y => ∑ k : Fin 2, ∫ z, prodFn k f (z, y) := by
    funext y
    rw [perturbation_eq_sum]
    simp only [h1]
  rw [hpert, integral_finsetSum _ (fun k _ => (hint k).integral_prod_right)]
  have h3 : ∀ k : Fin 2, ∫ y, ∫ z, prodFn k f (z, y) = ∫ z, ∫ y, prodFn k f (z, y) := fun k =>
    (integral_integral_swap (f := fun z y => prodFn k f (z, y)) (hint k)).symm
  simp_rw [h3]
  rw [← integral_finsetSum _ (fun k _ => (hint k).integral_prod_left)]
  have h4 : ∀ z : ℂ, ∑ k : Fin 2, ∫ y, prodFn k f (z, y) = (∫ y, symKernel z y) * f z := by
    intro z
    simp only [h2]
    rw [← Finset.sum_mul]
    congr 1
    unfold symKernel
    rw [integral_finsetSum _ (fun k _ => integrable_kernel_mul_gradS k z)]
  simp_rw [h4, integral_symKernel, zero_mul, integral_zero]

end UnforcedLeray.B0064
