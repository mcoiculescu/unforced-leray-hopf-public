import UnforcedLeray.Analysis.Heat.KernelNorm

/-!
# The heat kernel on `ℝ^d`, generic dimension (INF22 G1 definition, INF04 T1)


dimension Gaussian module serves INF04 T1–T2, INF22 G1 and the Gaussian part of INF02 T5.
This file is the definition and the zeroth-order facts (INF04 T1 of
`scoping/INF04-INF05-Heat.md` §5):

`gaussKernel d t x = (4πt)^{-d/2} exp(-|x|²/(4t))` on `Euc d = EuclideanSpace ℝ (Fin d)`
(the Euclidean norm, not the sup norm; critic §7, INF22 risk 4).

It is the heat kernel `G_t` of the manuscript (e.g. tex 466–492, B0722; tex 2454–2467, B0164;
tex 7447–7477, B0423; tex 7618–7690, B0448–B0450), INF04's `gauss d θ` and INF02's
`heatKernel d t`. Every statement assumes `0 < t`: for `t ≤ 0` the formula is a Lean junk value
(rpow of a nonpositive base, division by zero) and nothing is claimed about it.

Main results:
* `integral_gaussKernel`: `∫ G_t = 1`;
* `memLp_gaussKernel`: `G_t ∈ L^p` for every `p`;
* `eLpNorm_gaussKernel`: `‖G_t‖_{L^r} = (4πt)^{-(d/2)(1-1/r)} r^{-d/(2r)}` for `0 < r < ∞`,
  and `eLpNorm_gaussKernel_toReal` in INF04's form `gaussConst d r * t^{-(d/2)(1-1/r)}`;
* `eLpNorm_top_gaussKernel_le`: `‖G_t‖_∞ ≤ (4πt)^{-d/2}`;
* `integral_gaussKernel_mul_gaussKernel`: `∫ G_s(x-y) G_t(y) dy = G_{s+t}(x)` (adapted from the
  compiled 3D proof `lean/UnforcedLeray/Analysis/Heat/KernelSemigroup.lean`);
* `gaussKernel_scale`: `G_{λ²θ}(λx) = λ^{-d} G_θ(x)`;
* `gaussKernel_isometry`: invariance under linear isometries;
* `gaussKernel_three_eq`: `gaussKernel 3 = Heat.kernel` (bridge to the compiled kernel).
-/

noncomputable section

set_option autoImplicit false

namespace UnforcedLeray.Gaussian

open MeasureTheory Real
open scoped ENNReal RealInnerProductSpace

/-- Euclidean `ℝ^d` with its Euclidean norm. -/
abbrev Euc (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The heat kernel `G_t(x) = (4πt)^{-d/2} e^{-|x|²/(4t)}` on `ℝ^d` (INF22 G1, INF04 T1
`gauss`, INF02 T5 `heatKernel`). Meaningful for `t > 0` only. -/
def gaussKernel (d : ℕ) (t : ℝ) (x : Euc d) : ℝ :=
  (4 * π * t) ^ (-(d : ℝ) / 2) * Real.exp (-‖x‖ ^ 2 / (4 * t))

variable {d : ℕ}

theorem finrank_euc (d : ℕ) : Module.finrank ℝ (Euc d) = d := finrank_euclideanSpace_fin

theorem gaussKernel_pos {t : ℝ} (ht : 0 < t) (x : Euc d) : 0 < gaussKernel d t x :=
  mul_pos (Real.rpow_pos_of_pos (by positivity) _) (Real.exp_pos _)

theorem gaussKernel_nonneg {t : ℝ} (ht : 0 < t) (x : Euc d) : 0 ≤ gaussKernel d t x :=
  (gaussKernel_pos ht x).le

theorem gaussKernel_le {t : ℝ} (ht : 0 < t) (x : Euc d) :
    gaussKernel d t x ≤ (4 * π * t) ^ (-(d : ℝ) / 2) := by
  unfold gaussKernel
  apply mul_le_of_le_one_right (Real.rpow_pos_of_pos (by positivity) _).le
  rw [Real.exp_le_one_iff]
  have : 0 ≤ ‖x‖ ^ 2 / (4 * t) := by positivity
  rw [neg_div]; linarith

theorem contDiff_gaussKernel {n : WithTop ℕ∞} (t : ℝ) : ContDiff ℝ n (gaussKernel d t) := by
  unfold gaussKernel
  exact contDiff_const.mul (((contDiff_norm_sq ℝ).neg.div_const _).exp)

theorem continuous_gaussKernel (t : ℝ) : Continuous (gaussKernel d t) :=
  (contDiff_gaussKernel (n := 0) t).continuous

/-- `exp(-b|x|²)` is integrable on `ℝ^d` for `b > 0`. -/
theorem integrable_exp_neg_mul_sq_norm {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : Euc d => Real.exp (-b * ‖x‖ ^ 2)) := by
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (V := Euc d) (b := (b : ℂ)) (by simpa using hb) 0 0).re
  change Integrable (fun x : Euc d => (Complex.exp
    (-(b : ℂ) * ‖x‖ ^ 2 + 0 * inner ℝ (0 : Euc d) x)).re) at h
  simpa only [zero_mul, add_zero, ← Complex.ofReal_pow, ← Complex.ofReal_mul,
    ← Complex.ofReal_neg, ← Complex.ofReal_exp, Complex.ofReal_re] using h

/-- `∫_{ℝ^d} exp(-b|x|²) dx = (π/b)^{d/2}`. -/
theorem integral_exp_neg_mul_sq_norm {b : ℝ} (hb : 0 < b) :
    ∫ x : Euc d, Real.exp (-b * ‖x‖ ^ 2) = (π / b) ^ ((d : ℝ) / 2) := by
  rw [GaussianFourier.integral_rexp_neg_mul_sq_norm hb, finrank_euc]

theorem gaussKernel_eq_exp {t : ℝ} (x : Euc d) :
    gaussKernel d t x = (4 * π * t) ^ (-(d : ℝ) / 2) * Real.exp (-(4 * t)⁻¹ * ‖x‖ ^ 2) := by
  unfold gaussKernel; congr 2; ring

theorem integrable_gaussKernel {t : ℝ} (ht : 0 < t) : Integrable (gaussKernel d t) := by
  have : gaussKernel d t = fun x => (4 * π * t) ^ (-(d : ℝ) / 2) *
      Real.exp (-(4 * t)⁻¹ * ‖x‖ ^ 2) := funext fun x => gaussKernel_eq_exp x
  rw [this]
  exact (integrable_exp_neg_mul_sq_norm (by positivity)).const_mul _

/-- **INF04 T1 `integral_gauss`.** The heat kernel has unit mass. -/
theorem integral_gaussKernel {t : ℝ} (ht : 0 < t) : ∫ x : Euc d, gaussKernel d t x = 1 := by
  simp_rw [gaussKernel_eq_exp]
  rw [integral_const_mul, integral_exp_neg_mul_sq_norm (by positivity),
    show π / (4 * t)⁻¹ = 4 * π * t by field_simp, ← Real.rpow_add (by positivity),
    show -(d : ℝ) / 2 + (d : ℝ) / 2 = 0 by ring, Real.rpow_zero]

/-- `G_t(x)^r = (4πt)^{-dr/2} e^{-(r/(4t))|x|²}`. -/
theorem gaussKernel_rpow {t r : ℝ} (ht : 0 < t) (x : Euc d) :
    gaussKernel d t x ^ r =
      ((4 * π * t) ^ (-(d : ℝ) / 2)) ^ r * Real.exp (-(r / (4 * t)) * ‖x‖ ^ 2) := by
  rw [gaussKernel, Real.mul_rpow (Real.rpow_pos_of_pos (by positivity) _).le (Real.exp_pos _).le,
    ← Real.exp_mul]
  congr 2; ring

/-- **INF04 T1 `memLp_gauss`.** `G_t ∈ L^p(ℝ^d)` for every `p ∈ [0, ∞]`. -/
theorem memLp_gaussKernel {t : ℝ} (ht : 0 < t) (p : ℝ≥0∞) :
    MemLp (gaussKernel d t) p volume := by
  have hmeas : AEStronglyMeasurable (gaussKernel d t) volume :=
    (continuous_gaussKernel t).aestronglyMeasurable
  rcases eq_or_ne p 0 with rfl | hp0
  · exact memLp_zero_iff_aestronglyMeasurable.2 hmeas
  rcases eq_or_ne p ∞ with rfl | hpt
  · exact memLp_top_of_bound hmeas _ (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (gaussKernel_nonneg ht x)]; exact gaussKernel_le ht x)
  rw [← integrable_norm_rpow_iff hmeas hp0 hpt]
  have hr : 0 < p.toReal := ENNReal.toReal_pos hp0 hpt
  have : (fun x : Euc d => ‖gaussKernel d t x‖ ^ p.toReal) = fun x =>
      ((4 * π * t) ^ (-(d : ℝ) / 2)) ^ p.toReal *
        Real.exp (-(p.toReal / (4 * t)) * ‖x‖ ^ 2) := by
    funext x
    rw [Real.norm_of_nonneg (gaussKernel_nonneg ht x), gaussKernel_rpow ht]
  rw [this]
  exact (integrable_exp_neg_mul_sq_norm (by positivity)).const_mul _

/-- **INF04 T1 `eLpNorm_gauss`, exact form.** For `0 < r < ∞`,
`‖G_t‖_{L^r(ℝ^d)} = (4πt)^{-(d/2)(1-1/r)} r^{-d/(2r)}`. -/
theorem eLpNorm_gaussKernel {t r : ℝ} (ht : 0 < t) (hr : 0 < r) :
    eLpNorm (gaussKernel d t) (ENNReal.ofReal r) volume =
      ENNReal.ofReal ((4 * π * t) ^ (-(d : ℝ) / 2 * (1 - 1 / r)) * r ^ (-(d : ℝ) / (2 * r))) := by
  have hp0 : ENNReal.ofReal r ≠ 0 := by simpa using hr
  rw [(memLp_gaussKernel ht _).eLpNorm_eq_integral_rpow_norm hp0 ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hr.le]
  congr 1
  have hA : 0 < 4 * π * t := by positivity
  simp_rw [Real.norm_of_nonneg (gaussKernel_nonneg ht _), gaussKernel_rpow ht]
  rw [integral_const_mul, integral_exp_neg_mul_sq_norm (by positivity),
    show π / (r / (4 * t)) = 4 * π * t / r by field_simp,
    Real.mul_rpow (by positivity) (by positivity),
    Real.rpow_rpow_inv (Real.rpow_pos_of_pos hA _).le hr.ne',
    Real.div_rpow hA.le hr.le, Real.div_rpow (by positivity) (by positivity),
    ← Real.rpow_mul hA.le, ← Real.rpow_mul hr.le, mul_div_assoc', ← Real.rpow_add hA,
    div_eq_mul_inv, ← Real.rpow_neg hr.le]
  have hr0 : r ≠ 0 := hr.ne'
  congr 2 <;> field_simp <;> ring

/-- INF04's constant: `gaussConst d r = (4π)^{-(d/2)(1-1/r)} r^{-d/(2r)}`. -/
def gaussConst (d : ℕ) (r : ℝ) : ℝ :=
  (4 * π) ^ (-(d : ℝ) / 2 * (1 - 1 / r)) * r ^ (-(d : ℝ) / (2 * r))

/-- **INF04 T1 `eLpNorm_gauss`** in the scoping note's form, for `1 ≤ r < ∞`
(the proof needs only `0 < r`). -/
theorem eLpNorm_gaussKernel_toReal {t r : ℝ} (ht : 0 < t) (hr : 0 < r) :
    (eLpNorm (gaussKernel d t) (ENNReal.ofReal r) volume).toReal =
      gaussConst d r * t ^ (-(d : ℝ) / 2 * (1 - 1 / r)) := by
  rw [eLpNorm_gaussKernel ht hr, ENNReal.toReal_ofReal (by positivity), gaussConst,
    Real.mul_rpow (by positivity) ht.le]
  ring

/-- `‖G_t‖_{L^∞} ≤ (4πt)^{-d/2}`. -/
theorem eLpNorm_top_gaussKernel_le {t : ℝ} (ht : 0 < t) :
    eLpNorm (gaussKernel d t) ∞ volume ≤ ENNReal.ofReal ((4 * π * t) ^ (-(d : ℝ) / 2)) := by
  rw [eLpNorm_exponent_top]
  exact eLpNormEssSup_le_of_ae_bound (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (gaussKernel_nonneg ht x)]; exact gaussKernel_le ht x)

/-! ### Convolution (semigroup) law. Adapted from the compiled 3D proof
`lean/UnforcedLeray/Analysis/Heat/KernelSemigroup.lean` (variance `q = 4t` there). -/

/-- Completing the square, with the correct vector centre. -/
theorem exponent_product {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (x y : Euc d) :
    -‖x - y‖ ^ 2 / (4 * s) + -‖y‖ ^ 2 / (4 * t) =
      -‖x‖ ^ 2 / (4 * (s + t)) + -‖y - (t / (s + t)) • x‖ ^ 2 / (4 * (s * t / (s + t))) := by
  simp only [norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs, real_inner_comm y x]
  field_simp
  ring

theorem gaussKernel_product {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (x y : Euc d) :
    gaussKernel d s (x - y) * gaussKernel d t y =
      gaussKernel d (s + t) x * gaussKernel d (s * t / (s + t)) (y - (t / (s + t)) • x) := by
  unfold gaussKernel
  have hst : 0 < s * t / (s + t) := by positivity
  have hnorm : (4 * π * s) ^ (-(d : ℝ) / 2) * (4 * π * t) ^ (-(d : ℝ) / 2) =
      (4 * π * (s + t)) ^ (-(d : ℝ) / 2) * (4 * π * (s * t / (s + t))) ^ (-(d : ℝ) / 2) := by
    rw [← Real.mul_rpow (by positivity) (by positivity),
      ← Real.mul_rpow (by positivity) (by positivity)]
    congr 1; field_simp
  calc _ = ((4 * π * s) ^ (-(d : ℝ) / 2) * (4 * π * t) ^ (-(d : ℝ) / 2)) *
        Real.exp (-‖x - y‖ ^ 2 / (4 * s) + -‖y‖ ^ 2 / (4 * t)) := by rw [Real.exp_add]; ring
    _ = _ := by rw [hnorm, exponent_product hs ht, Real.exp_add]; ring

theorem integrable_gaussKernel_product {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (x : Euc d) :
    Integrable (fun y : Euc d => gaussKernel d s (x - y) * gaussKernel d t y) := by
  simp_rw [gaussKernel_product hs ht x]
  exact ((integrable_gaussKernel (by positivity)).comp_sub_right _).const_mul _

/-- **INF04 T1 `gauss_conv`.** `∫ G_s(x-y) G_t(y) dy = G_{s+t}(x)`. -/
theorem integral_gaussKernel_mul_gaussKernel {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (x : Euc d) :
    ∫ y : Euc d, gaussKernel d s (x - y) * gaussKernel d t y = gaussKernel d (s + t) x := by
  simp_rw [gaussKernel_product hs ht x]
  rw [integral_const_mul, integral_sub_right_eq_self, integral_gaussKernel (by positivity),
    mul_one]

/-- **INF04 T1 `gauss_scale`.** `G_{λ²θ}(λx) = λ^{-d} G_θ(x)` for `λ, θ > 0`. -/
theorem gaussKernel_scale {lam θ : ℝ} (hlam : 0 < lam) (hθ : 0 < θ) (x : Euc d) :
    gaussKernel d (lam ^ 2 * θ) (lam • x) = lam ^ (-(d : ℝ)) * gaussKernel d θ x := by
  unfold gaussKernel
  have h1 : -‖lam • x‖ ^ 2 / (4 * (lam ^ 2 * θ)) = -‖x‖ ^ 2 / (4 * θ) := by
    rw [norm_smul, Real.norm_of_nonneg hlam.le]; field_simp
  have h2 : (lam ^ 2) ^ (-(d : ℝ) / 2) = lam ^ (-(d : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hlam.le]; push_cast; ring_nf
  rw [h1, show 4 * π * (lam ^ 2 * θ) = lam ^ 2 * (4 * π * θ) by ring,
    Real.mul_rpow (by positivity) (by positivity), h2]
  ring

/-- **INF04 T1 `gauss_isometry`.** Rotation invariance. -/
theorem gaussKernel_isometry (g : Euc d ≃ₗᵢ[ℝ] Euc d) (t : ℝ) (x : Euc d) :
    gaussKernel d t (g x) = gaussKernel d t x := by
  simp [gaussKernel]

/-- `G_t(-x) = G_t(x)`. -/
theorem gaussKernel_neg (t : ℝ) (x : Euc d) : gaussKernel d t (-x) = gaussKernel d t x := by
  simp [gaussKernel]

/-- **G1 / INF04 T1 `gauss_three`.** Bridge to the compiled kernel
`UnforcedLeray.Heat.kernel` (`lean/UnforcedLeray/Analysis/Heat/KernelNorm.lean`), for every `t`. -/
theorem gaussKernel_three_eq : gaussKernel 3 = Heat.kernel := by
  funext t x
  rw [Heat.kernel_formula, gaussKernel]
  have : -‖x‖ ^ 2 / (4 * t) = -(4 * t)⁻¹ * ‖x‖ ^ 2 := by ring
  rw [this]; norm_num

end UnforcedLeray.Gaussian
