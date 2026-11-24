import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Std.Tactic.BVDecide.LRAT.Internal.Formula.RupAddResult

/-!
# INF22 K8, part 1: the cylinder Biot–Savart kernel


(§5, bypass BP7; decision D14 of `scoping/README.md`: the cylinder Biot–Savart kernel is defined once,
here, with its image and mode expansions, and INF13 CY11 builds the operator K_c ω on top of it).

In complex notation z = q + iη on (ℝ/cℤ) × ℝ, the kernel is

  K_c(z) = (2πi)^{-1} (π/c) cot(πz/c) = (2πi)^{-1} (1/z + Σ_{n ≥ 1} [1/(z − nc) + 1/(z + nc)]),

the periodic sum of the planar kernel (2πi z)^{-1} with paired images (Mathlib's Mittag-Leffler
expansion `cot_series_rep`). This module proves

* `cylinderBS_eq_paired`: the paired-image formula (for z/c ∉ ℤ);
* `cylinderBS_periodic`: c-periodicity in q;
* `norm_cot_le`: ‖cot w‖ ≤ π/‖w‖ + 2 on the strip |Re w| ≤ π/2;
* `norm_cylinderBS_le`: the uniform near/far bound ‖K_c(z)‖ ≤ C(‖z‖^{-1} + 1) on the centred cell
  |Re z| ≤ c/2, uniformly in c ≥ 1 (blueprint units B0592, tex 9594–9608, and B0658,
  tex 13917–13925).

Junk values: `Complex.cot` at a pole is `cos/0 = 0`; every statement below excludes z ∈ cℤ.
The norm on ℂ is the Euclidean modulus, so no sup-norm issue arises (critic D1 domain-norm item).
-/

set_option autoImplicit false

noncomputable section

open Filter Topology

namespace UnforcedLeray.Kernels

/-- The cylinder Biot–Savart kernel K_c(z) = (2πi)^{-1} (π/c) cot(πz/c) (INF22 K8, BP7). -/
def cylinderBS (c : ℝ) (z : ℂ) : ℂ :=
  (2 * Real.pi * Complex.I)⁻¹ * ((Real.pi / c) * Complex.cot (Real.pi * z / c))

/-- The paired-image (Mittag-Leffler) formula for K_c (INF22 K8 `cylinderBS_eq_paired`). -/
theorem cylinderBS_eq_paired {c : ℝ} (hc : 0 < c) {z : ℂ}
    (hz : z / c ∈ Complex.integerComplement) :
    cylinderBS c z = (2 * Real.pi * Complex.I)⁻¹ *
      (1 / z + ∑' n : ℕ+, (1 / (z - n * c) + 1 / (z + n * c))) := by
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have h := cot_series_rep hz
  unfold cylinderBS
  congr 1
  have h1 : (Real.pi : ℂ) * z / c = Real.pi * (z / c) := by ring
  rw [h1]
  have h2 : ((Real.pi : ℝ) : ℂ) / c * Complex.cot (Real.pi * (z / c)) =
      (1 / c) * (Real.pi * Complex.cot (Real.pi * (z / c))) := by ring
  rw [h2, h, mul_add, ← tsum_mul_left]
  congr 1
  · field_simp
  · congr 1
    funext n
    have e1 : z / c - n = (z - n * c) / c := by field_simp
    have e2 : z / c + n = (z + n * c) / c := by field_simp
    rw [e1, e2, one_div_div, one_div_div, mul_add, ← mul_div_assoc, ← mul_div_assoc,
      one_div_mul_cancel hc0]

/-- K_c is c-periodic (INF22 K8 `cylinderBS_periodic`). -/
theorem cylinderBS_periodic (c : ℝ) (z : ℂ) : cylinderBS c (z + c) = cylinderBS c z := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  unfold cylinderBS
  have h1 : (Real.pi : ℂ) * (z + c) / c = Real.pi * z / c + Real.pi := by field_simp
  rw [h1, Complex.cot_eq_cos_div_sin, Complex.cot_eq_cos_div_sin, Complex.cos_add_pi,
    Complex.sin_add_pi, neg_div_neg_eq]

/-! ### The strip bound for cot -/

theorem sin_eq_re_im (w : ℂ) : Complex.sin w =
    ((Real.sin w.re * Real.cosh w.im : ℝ) : ℂ) + ((Real.cos w.re * Real.sinh w.im : ℝ) : ℂ) *
      Complex.I := by
  rw [Complex.sin_eq]; push_cast; ring

theorem cos_eq_re_im (w : ℂ) : Complex.cos w =
    ((Real.cos w.re * Real.cosh w.im : ℝ) : ℂ) + ((-(Real.sin w.re * Real.sinh w.im) : ℝ) : ℂ) *
      Complex.I := by
  rw [Complex.cos_eq]; push_cast; ring

theorem norm_sin_sq (w : ℂ) : ‖Complex.sin w‖ ^ 2 = Real.sin w.re ^ 2 + Real.sinh w.im ^ 2 := by
  rw [sin_eq_re_im, Complex.sq_norm, Complex.normSq_add_mul_I]
  linear_combination Real.sin w.re ^ 2 * Real.cosh_sq w.im +
    Real.sinh w.im ^ 2 * Real.sin_sq_add_cos_sq w.re

theorem norm_cos_sq (w : ℂ) : ‖Complex.cos w‖ ^ 2 = Real.cos w.re ^ 2 + Real.sinh w.im ^ 2 := by
  rw [cos_eq_re_im, Complex.sq_norm, Complex.normSq_add_mul_I]
  linear_combination Real.cos w.re ^ 2 * Real.cosh_sq w.im +
    Real.sinh w.im ^ 2 * Real.sin_sq_add_cos_sq w.re

theorem norm_sq_eq_re_im (w : ℂ) : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]; ring

/-- Jordan's inequality in squared form: sin² x ≥ (2/π)² x² for |x| ≤ π/2. -/
theorem sin_sq_ge {x : ℝ} (hx : |x| ≤ Real.pi / 2) : (2 / Real.pi) ^ 2 * x ^ 2 ≤ Real.sin x ^ 2 := by
  have hpi := Real.pi_pos
  rcases le_or_gt 0 x with h0 | h0
  · have h := Real.mul_le_sin h0 (by rw [abs_of_nonneg h0] at hx; exact hx)
    have : 0 ≤ 2 / Real.pi * x := by positivity
    nlinarith
  · have h := Real.mul_le_sin (x := -x) (by linarith) (by rw [abs_of_neg h0] at hx; exact hx)
    rw [Real.sin_neg] at h
    have : 0 ≤ 2 / Real.pi * -x := by have : 0 < -x := by linarith
                                      positivity
    nlinarith

theorem sinh_sq_ge (y : ℝ) : y ^ 2 ≤ Real.sinh y ^ 2 := by
  rcases le_or_gt 0 y with h0 | h0
  · have h := Real.self_le_sinh_iff.2 h0
    nlinarith
  · have h := Real.self_le_sinh_iff.2 (show 0 ≤ -y by linarith)
    rw [Real.sinh_neg] at h
    nlinarith

theorem cosh_one_le_two : Real.cosh 1 ≤ 2 := by
  rw [Real.cosh_eq]
  have h1 := Real.exp_one_lt_d9
  have h2 : Real.exp (-1) ≤ 1 := Real.exp_le_one_iff.2 (by norm_num)
  linarith

/-- ‖cot w‖ ≤ π/‖w‖ + 2 on the strip |Re w| ≤ π/2, w ≠ 0 (BP7). -/
theorem norm_cot_le {w : ℂ} (hw : w ≠ 0) (hre : |w.re| ≤ Real.pi / 2) :
    ‖Complex.cot w‖ ≤ Real.pi / ‖w‖ + 2 := by
  have hpi := Real.pi_pos
  have hpi3 := Real.pi_gt_three
  have hwn : 0 < ‖w‖ := norm_pos_iff.2 hw
  set x := w.re
  set y := w.im
  have hs := norm_sin_sq w
  have hc := norm_cos_sq w
  have hw2 := norm_sq_eq_re_im w
  have hJ := sin_sq_ge hre
  have hS := sinh_sq_ge y
  have hcos1 : Real.cos x ^ 2 ≤ 1 := by
    have := Real.sin_sq_add_cos_sq x; nlinarith [sq_nonneg (Real.sin x)]
  have hsin_pos : 0 < ‖Complex.sin w‖ := by
    have hk : (2 / Real.pi) ^ 2 * ‖w‖ ^ 2 ≤ ‖Complex.sin w‖ ^ 2 := by
      have h4 : (2 / Real.pi) ^ 2 ≤ 1 := by
        rw [div_pow]; rw [div_le_one (by positivity)]; nlinarith
      rw [hw2, hs]
      have : 0 ≤ y ^ 2 := sq_nonneg y
      nlinarith
    have h4 : 0 < (2 / Real.pi) ^ 2 * ‖w‖ ^ 2 := by positivity
    have h5 : 0 < ‖Complex.sin w‖ ^ 2 := lt_of_lt_of_le h4 hk
    exact lt_of_le_of_ne (norm_nonneg _) (fun h => by rw [← h] at h5; simp at h5)
  rw [Complex.cot_eq_cos_div_sin, norm_div, div_le_iff₀ hsin_pos]
  rcases le_or_gt |y| 1 with hy | hy
  · -- near part: ‖cos w‖ ≤ 2 and ‖sin w‖ ≥ (2/π)‖w‖
    have hcosh : Real.cosh y ≤ 2 :=
      (Real.cosh_le_cosh.2 (by rw [abs_one]; exact hy)).trans cosh_one_le_two
    have hcos : ‖Complex.cos w‖ ≤ 2 := by
      have h1 : ‖Complex.cos w‖ ^ 2 ≤ 2 ^ 2 := by
        rw [hc]
        have := Real.cosh_sq y
        have : 0 ≤ Real.cosh y := (Real.cosh_pos y).le
        nlinarith
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by norm_num) two_ne_zero).1 h1
    have hsin : 2 / Real.pi * ‖w‖ ≤ ‖Complex.sin w‖ := by
      have h1 : (2 / Real.pi * ‖w‖) ^ 2 ≤ ‖Complex.sin w‖ ^ 2 := by
        rw [mul_pow, hw2, hs]
        have h4 : (2 / Real.pi) ^ 2 ≤ 1 := by
          rw [div_pow]; rw [div_le_one (by positivity)]; nlinarith
        have : 0 ≤ y ^ 2 := sq_nonneg y
        nlinarith
      exact (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).1 h1
    calc ‖Complex.cos w‖ ≤ 2 := hcos
      _ = Real.pi / ‖w‖ * (2 / Real.pi * ‖w‖) := by field_simp
      _ ≤ Real.pi / ‖w‖ * ‖Complex.sin w‖ := by gcongr
      _ ≤ (Real.pi / ‖w‖ + 2) * ‖Complex.sin w‖ := by
        have := norm_nonneg (Complex.sin w)
        nlinarith
  · -- far part: ‖cos w‖ ≤ 2 ‖sin w‖
    have hy2 : 1 ≤ y ^ 2 := by
      have : 1 ≤ |y| := hy.le
      nlinarith [sq_abs y, abs_nonneg y]
    have h1 : ‖Complex.cos w‖ ^ 2 ≤ (2 * ‖Complex.sin w‖) ^ 2 := by
      rw [mul_pow, hc, hs]
      nlinarith [sq_nonneg (Real.sin x)]
    have h2 : ‖Complex.cos w‖ ≤ 2 * ‖Complex.sin w‖ :=
      (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h1
    have : 0 ≤ Real.pi / ‖w‖ * ‖Complex.sin w‖ := by positivity
    nlinarith

/-- INF22 K8 `norm_cylinderBS_le` (B0592, B0658): on the centred cell |Re z| ≤ c/2, uniformly in
c ≥ 1, ‖K_c(z)‖ ≤ ‖z‖^{-1} + 1 (near part ≤ C/|z|, far part bounded). -/
theorem norm_cylinderBS_le' {c : ℝ} (hc : 1 ≤ c) {z : ℂ} (hre : |z.re| ≤ c / 2) (hz : z ≠ 0) :
    ‖cylinderBS c z‖ ≤ 1 * (‖z‖⁻¹ + 1) := by
  have hpi := Real.pi_pos
  have hc0 : 0 < c := by linarith
  have hzn : 0 < ‖z‖ := norm_pos_iff.2 hz
  set w : ℂ := Real.pi * z / c with hw_def
  have hw : w ≠ 0 := by
    rw [hw_def]
    exact div_ne_zero (mul_ne_zero (by exact_mod_cast hpi.ne') hz) (by exact_mod_cast hc0.ne')
  have hwre : w.re = Real.pi * z.re / c := by
    rw [hw_def]
    simp [Complex.div_re, Complex.normSq_ofReal]
    field_simp
  have hwn : ‖w‖ = Real.pi * ‖z‖ / c := by
    rw [hw_def, norm_div, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hpi.le,
      Real.norm_of_nonneg hc0.le]
  have hstrip : |w.re| ≤ Real.pi / 2 := by
    rw [hwre, abs_div, abs_mul, abs_of_pos hpi, abs_of_pos hc0, div_le_iff₀ hc0]
    have := mul_le_mul_of_nonneg_left hre hpi.le
    linarith
  have hcot := norm_cot_le hw hstrip
  rw [hwn] at hcot
  unfold cylinderBS
  rw [← hw_def, norm_mul, norm_mul, norm_inv, norm_mul, norm_mul, Complex.norm_I,
    Complex.norm_real, Complex.norm_ofNat, norm_div, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg hpi.le, Real.norm_of_nonneg hc0.le, mul_one]
  have hcotn := norm_nonneg (Complex.cot w)
  have key : Real.pi / (Real.pi * ‖z‖ / c) = c / ‖z‖ := by field_simp
  rw [key] at hcot
  calc (2 * Real.pi)⁻¹ * (Real.pi / c * ‖Complex.cot w‖)
      = ‖Complex.cot w‖ / (2 * c) := by field_simp
    _ ≤ (c / ‖z‖ + 2) / (2 * c) := by gcongr
    _ = (1 / 2) * ‖z‖⁻¹ + 1 / c := by field_simp
    _ ≤ 1 * (‖z‖⁻¹ + 1) := by
      have : 1 / c ≤ 1 := by rw [div_le_one hc0]; exact hc
      have : 0 ≤ ‖z‖⁻¹ := inv_nonneg.2 hzn.le
      linarith

/-- INF22 K8 `norm_cylinderBS_le` in the quantifier form of the note. -/
theorem norm_cylinderBS_le : ∃ C, ∀ c : ℝ, 1 ≤ c → ∀ z : ℂ, |z.re| ≤ c / 2 → z ≠ 0 →
    ‖cylinderBS c z‖ ≤ C * (‖z‖⁻¹ + 1) :=
  ⟨1, fun _ hc _ hre hz => norm_cylinderBS_le' hc hre hz⟩

end UnforcedLeray.Kernels
