import UnforcedLeray.Units.B0579
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Algebra.Order.Round

/-!
# B0592 helper: the cylinder Biot–Savart kernel and its pointwise bounds

Helper for blueprint unit **B0592** (`prepared:p4.4a`, `paper/main.tex` lines 9594–9608).
The manuscript's sentence (lines 9594–9596): "The cylinder Biot–Savart kernel is locally bounded
by `C/|x|`, with uniformly bounded local `L¹` norm, and uniformly bounded away from the diagonal
for `c ≥ 2`." This file proves exactly these kernel facts (blueprint infrastructure INF22,
"periodic Biot–Savart kernel (`log|sin(πz/c)|` stream) and its bounds").

**The kernel.** On the cylinder `C_c = (ℝ/cℤ) × ℝ` (`paper/main.tex:2106`) with `x = (q, η)`,
`K_c = ∇^⊥Δ^{-1}` (`∇^⊥ = (-∂_η, ∂_q)`, the planar convention of `paper/main.tex:662`, unit
B0009) has the stream function
`G_c(q, η) = (4π)^{-1} log(cosh(2πη/c) - cos(2πq/c)) = (2π)^{-1} log|sin(π(q+iη)/c)| + const`,
the `c`-periodic Green function, and kernel
`K_c(q, η) = ∇^⊥G_c = (2c)^{-1} (-sinh(2πη/c), sin(2πq/c)) / (cosh(2πη/c) - cos(2πq/c))`.
A velocity vector `(u₁, u₂)` is the complex number `u₁ + i u₂` (as in unit B0009), so
`bsKernel c z : ℂ` and `‖bsKernel c z‖` is the Euclidean length. `hasDerivAt_stream_fst`,
`hasDerivAt_stream_snd` check `bsKernel = ∇^⊥ stream` off the lattice `cℤ × {0}`;
`bsKernel_sub_int` checks `c`-periodicity in `q`. On the lattice the denominator vanishes and
Lean's division returns `0` (a null set; the integrals below never see it).

**Bounds.** With `a = πq/c`, `b = πη/c` one has `den = 2(sin²a + sinh²b)` and
`‖K_c‖² = (cos²a + sinh²b) / (4c²(sin²a + sinh²b))`. On the centered strip `|q| ≤ c/2`,
Jordan's inequality and `|sinh b| ≥ |b|` give `sin²a + sinh²b ≥ 4|x|²/c²`, whence
`‖K_c(x)‖ ≤ 1/(2c) + 1/(4|x|)` (`norm_bsKernel_le_reduced`; `|x|` is the sup norm of
`ℝ × ℝ`, which is at most the Euclidean norm). For `c ≥ 2` this is the manuscript's statement:
`‖K_c(x)‖ ≤ 1/2 + nearKernel(x)/4` with `nearKernel = 1_{|x|<1} |x|^{-1}` (locally `C/|x|`;
bounded by `1/2` away from the diagonal), and `nearKernel` has finite `L¹` norm
(`integrable_nearKernel`), independent of `c`. `norm_bsKernel_le_sum` transports the bound to
`x` in a fixed box and `y` in the centered cell: the relevant periodic images are the shifts
`j ∈ [-N, N]`, `N = ⌈R/2⌉ + 1`, independent of `c ≥ 2`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Real

namespace UnforcedLeray.B0592

open UnforcedLeray.B0579 (Plane cell jb jb_pos)

/-! ### The kernel and its stream function -/

/-- The denominator `cosh(2πη/c) - cos(2πq/c) = 2|sin(π(q + iη)/c)|²`. -/
def den (c : ℝ) (z : Plane) : ℝ :=
  Real.cosh (2 * π * z.2 / c) - Real.cos (2 * π * z.1 / c)

/-- **The cylinder Biot–Savart kernel** `K_c = ∇^⊥ G_c` (`paper/main.tex:9594`, INF22), as the
complex number `K₁ + i K₂`:
`K_c(q, η) = (-sinh(2πη/c) + i sin(2πq/c)) / (2c (cosh(2πη/c) - cos(2πq/c)))`. -/
def bsKernel (c : ℝ) (z : Plane) : ℂ :=
  ⟨-Real.sinh (2 * π * z.2 / c) / (2 * c * den c z),
    Real.sin (2 * π * z.1 / c) / (2 * c * den c z)⟩

/-- The periodic stream function `G_c = (4π)^{-1} log(cosh(2πη/c) - cos(2πq/c))`, i.e.
`(2π)^{-1} log|sin(π(q + iη)/c)| + (4π)^{-1} log 2`. -/
def stream (c : ℝ) (z : Plane) : ℝ := Real.log (den c z) / (4 * π)

/-- `∂_q G_c = K₂` off the lattice. -/
theorem hasDerivAt_stream_fst {c : ℝ} (hc : c ≠ 0) {q η : ℝ} (h : den c (q, η) ≠ 0) :
    HasDerivAt (fun t => stream c (t, η)) (bsKernel c (q, η)).im q := by
  have hlin : HasDerivAt (fun t : ℝ => 2 * π * t / c) (2 * π * 1 / c) q :=
    ((hasDerivAt_id q).const_mul (2 * π)).div_const c
  have hden : HasDerivAt (fun t : ℝ => den c (t, η))
      (-(-Real.sin (2 * π * q / c) * (2 * π * 1 / c))) q := by
    have := hlin.cos.const_sub (Real.cosh (2 * π * η / c))
    simpa [den] using this
  have hlog : HasDerivAt (fun t => stream c (t, η))
      (-(-Real.sin (2 * π * q / c) * (2 * π * 1 / c)) / den c (q, η) / (4 * π)) q :=
    (hden.log h).div_const (4 * π)
  refine hlog.congr_deriv ?_
  have e : (bsKernel c (q, η)).im = Real.sin (2 * π * q / c) / (2 * c * den c (q, η)) := rfl
  rw [e]
  have hpi : π ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

/-- `∂_η G_c = -K₁` off the lattice. -/
theorem hasDerivAt_stream_snd {c : ℝ} (hc : c ≠ 0) {q η : ℝ} (h : den c (q, η) ≠ 0) :
    HasDerivAt (fun t => stream c (q, t)) (-(bsKernel c (q, η)).re) η := by
  have hlin : HasDerivAt (fun t : ℝ => 2 * π * t / c) (2 * π * 1 / c) η :=
    ((hasDerivAt_id η).const_mul (2 * π)).div_const c
  have hden : HasDerivAt (fun t : ℝ => den c (q, t))
      (Real.sinh (2 * π * η / c) * (2 * π * 1 / c)) η := by
    have := hlin.cosh.sub_const (Real.cos (2 * π * q / c))
    simpa [den] using this
  have hlog : HasDerivAt (fun t => stream c (q, t))
      (Real.sinh (2 * π * η / c) * (2 * π * 1 / c) / den c (q, η) / (4 * π)) η :=
    (hden.log h).div_const (4 * π)
  refine hlog.congr_deriv ?_
  have e : (bsKernel c (q, η)).re = -Real.sinh (2 * π * η / c) / (2 * c * den c (q, η)) := rfl
  rw [e]
  have hpi : π ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

/-- `c`-periodicity in `q`. -/
theorem bsKernel_sub_int {c : ℝ} (hc : c ≠ 0) (z : Plane) (k : ℤ) :
    bsKernel c (z.1 - k * c, z.2) = bsKernel c z := by
  have h : 2 * π * (z.1 - k * c) / c = 2 * π * z.1 / c - k * (2 * π) := by
    field_simp
  simp only [bsKernel, den, h, Real.sin_sub_int_mul_two_pi, Real.cos_sub_int_mul_two_pi]

theorem measurable_bsKernel (c : ℝ) : Measurable (bsKernel c) := by
  have h1 : Measurable fun z : Plane => -Real.sinh (2 * π * z.2 / c) / (2 * c * den c z) := by
    unfold den
    fun_prop
  have h2 : Measurable fun z : Plane => Real.sin (2 * π * z.1 / c) / (2 * c * den c z) := by
    unfold den
    fun_prop
  have e : bsKernel c = fun z => ((-Real.sinh (2 * π * z.2 / c) / (2 * c * den c z) : ℝ) : ℂ) +
      ((Real.sin (2 * π * z.1 / c) / (2 * c * den c z) : ℝ) : ℂ) * Complex.I := by
    funext z
    apply Complex.ext <;>
      simp only [bsKernel, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im] <;> ring
  rw [e]
  exact h1.complex_ofReal.add (h2.complex_ofReal.mul_const _)

/-! ### The exact norm -/

theorem den_eq (c : ℝ) (z : Plane) :
    den c z = 2 * (Real.sin (π * z.1 / c) ^ 2 + Real.sinh (π * z.2 / c) ^ 2) := by
  have h1 : 2 * π * z.2 / c = 2 * (π * z.2 / c) := by ring
  have h2 : 2 * π * z.1 / c = 2 * (π * z.1 / c) := by ring
  rw [den, h1, h2, Real.cosh_two_mul, Real.cos_two_mul, Real.cosh_sq, Real.cos_sq']
  ring

theorem num_sq (c : ℝ) (z : Plane) :
    Real.sinh (2 * π * z.2 / c) ^ 2 + Real.sin (2 * π * z.1 / c) ^ 2 =
      4 * (Real.sin (π * z.1 / c) ^ 2 + Real.sinh (π * z.2 / c) ^ 2) *
        (Real.cos (π * z.1 / c) ^ 2 + Real.sinh (π * z.2 / c) ^ 2) := by
  have h1 : 2 * π * z.2 / c = 2 * (π * z.2 / c) := by ring
  have h2 : 2 * π * z.1 / c = 2 * (π * z.1 / c) := by ring
  rw [h1, h2, Real.sinh_two_mul, Real.sin_two_mul]
  have e1 := Real.cosh_sq (π * z.2 / c)
  have e2 := Real.sin_sq_add_cos_sq (π * z.1 / c)
  linear_combination (4 * Real.sinh (π * z.2 / c) ^ 2) * e1 -
    (4 * Real.sinh (π * z.2 / c) ^ 2) * e2

theorem norm_bsKernel_sq (c : ℝ) (z : Plane) :
    ‖bsKernel c z‖ ^ 2 =
      (Real.sinh (2 * π * z.2 / c) ^ 2 + Real.sin (2 * π * z.1 / c) ^ 2) /
        (2 * c * den c z) ^ 2 := by
  rw [Complex.sq_norm, bsKernel, Complex.normSq_mk]
  ring

/-- `‖(q, η)‖² ≤ q² + η²` for the sup norm of `ℝ × ℝ`. -/
theorem norm_sq_le (z : Plane) : ‖z‖ ^ 2 ≤ z.1 ^ 2 + z.2 ^ 2 := by
  rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
  rcases le_total |z.1| |z.2| with h | h
  · rw [max_eq_right h, sq_abs]
    nlinarith [sq_nonneg z.1]
  · rw [max_eq_left h, sq_abs]
    nlinarith [sq_nonneg z.2]

/-- Jordan: `4q² ≤ c² sin²(πq/c)` for `|q| ≤ c/2`. -/
theorem sin_sq_lower {c : ℝ} (hc : 0 < c) {q : ℝ} (hq : |q| ≤ c / 2) :
    4 * q ^ 2 ≤ c ^ 2 * Real.sin (π * q / c) ^ 2 := by
  set a := π * q / c with ha
  have habs : |a| = π * |q| / c := by
    rw [ha, abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos hc]
  have hle : |a| ≤ π / 2 := by
    rw [habs, div_le_iff₀ hc]
    nlinarith [mul_le_mul_of_nonneg_left hq Real.pi_pos.le]
  have key : 2 / π * |a| ≤ |Real.sin a| := by
    rcases le_total 0 a with h0 | h0
    · rw [abs_of_nonneg h0]
      exact (Real.mul_le_sin h0 (by rw [abs_of_nonneg h0] at hle; exact hle)).trans
        (le_abs_self _)
    · rw [abs_of_nonpos h0]
      have := Real.mul_le_sin (neg_nonneg.mpr h0) (by rw [abs_of_nonpos h0] at hle; exact hle)
      rw [Real.sin_neg] at this
      exact this.trans (neg_le_abs _)
  have e : 2 / π * |a| = 2 * |q| / c := by
    rw [habs]
    field_simp
  rw [e, div_le_iff₀ hc] at key
  have h2 : (2 * |q|) ^ 2 ≤ (|Real.sin a| * c) ^ 2 :=
    pow_le_pow_left₀ (by positivity) key 2
  rw [mul_pow, mul_pow, sq_abs, sq_abs] at h2
  linarith

/-- `4η² ≤ c² sinh²(πη/c)`. -/
theorem sinh_sq_lower {c : ℝ} (hc : 0 < c) (η : ℝ) :
    4 * η ^ 2 ≤ c ^ 2 * Real.sinh (π * η / c) ^ 2 := by
  set b := π * η / c with hb
  have h1 : |b| ≤ |Real.sinh b| := by
    rw [Real.abs_sinh]
    exact Real.self_le_sinh_iff.mpr (abs_nonneg b)
  have h2 : b ^ 2 ≤ Real.sinh b ^ 2 := by
    have := pow_le_pow_left₀ (abs_nonneg b) h1 2
    rwa [sq_abs, sq_abs] at this
  have h3 : c ^ 2 * b ^ 2 = π ^ 2 * η ^ 2 := by
    rw [hb]
    field_simp
  have hpi : (4 : ℝ) ≤ π ^ 2 := by nlinarith [Real.two_le_pi]
  nlinarith [mul_le_mul_of_nonneg_left h2 (sq_nonneg c), sq_nonneg η]

/-- The algebra behind `norm_bsKernel_sq_le`, with `s = sin²a`, `h = sinh²b`, `co = cos²a`,
`n = |x|²`. -/
theorem alg_bound {c s h co n : ℝ} (hc : 0 < c) (hs : 0 ≤ s) (hco : co ≤ 1) (hS : 0 < s + h)
    (hn : 0 < n)
    (hlow : 16 * n ≤ 4 * c ^ 2 * (s + h)) :
    4 * (s + h) * (co + h) / (2 * c * (2 * (s + h))) ^ 2 ≤ 1 / (4 * c ^ 2) + 1 / (16 * n) := by
  have hc' : c ≠ 0 := hc.ne'
  have hS' : s + h ≠ 0 := hS.ne'
  have hd : 0 < 4 * c ^ 2 * (s + h) := by positivity
  calc 4 * (s + h) * (co + h) / (2 * c * (2 * (s + h))) ^ 2
        = (co + h) / (4 * c ^ 2 * (s + h)) := by
          field_simp
          ring
    _ ≤ (1 + (s + h)) / (4 * c ^ 2 * (s + h)) :=
          div_le_div_of_nonneg_right (by linarith) hd.le
    _ = 1 / (4 * c ^ 2) + 1 / (4 * c ^ 2 * (s + h)) := by
          field_simp
          ring
    _ ≤ 1 / (4 * c ^ 2) + 1 / (16 * n) := by
          have := one_div_le_one_div_of_le (by positivity : (0 : ℝ) < 16 * n) hlow
          linarith

/-- **Local bound** on the centered strip: `‖K_c(x)‖² ≤ 1/(4c²) + 1/(16|x|²)` for `|q| ≤ c/2`. -/
theorem norm_bsKernel_sq_le {c : ℝ} (hc : 0 < c) {z : Plane} (hz : |z.1| ≤ c / 2) :
    ‖bsKernel c z‖ ^ 2 ≤ 1 / (4 * c ^ 2) + 1 / (16 * ‖z‖ ^ 2) := by
  have hsin := sin_sq_lower hc hz
  have hsinh := sinh_sq_lower hc z.2
  have hzz := norm_sq_le z
  rw [norm_bsKernel_sq, num_sq, den_eq]
  by_cases hS0 : Real.sin (π * z.1 / c) ^ 2 + Real.sinh (π * z.2 / c) ^ 2 = 0
  · rw [hS0]
    have e : (4 : ℝ) * 0 * (Real.cos (π * z.1 / c) ^ 2 + Real.sinh (π * z.2 / c) ^ 2) /
        (2 * c * (2 * 0)) ^ 2 = 0 := by simp
    rw [e]
    positivity
  have hS : 0 < Real.sin (π * z.1 / c) ^ 2 + Real.sinh (π * z.2 / c) ^ 2 :=
    lt_of_le_of_ne (by positivity) (Ne.symm hS0)
  have hz0 : 0 < ‖z‖ := by
    rcases (norm_nonneg z).eq_or_lt with h0 | h0
    · exfalso
      have hz' : z = 0 := norm_eq_zero.mp h0.symm
      apply hS0
      simp [hz']
    · exact h0
  refine alg_bound hc (sq_nonneg _) (Real.cos_sq_le_one _) hS (by positivity) ?_
  nlinarith

/-- `‖K_c(x)‖ ≤ 1/(2c) + 1/(4|x|)` for `|q| ≤ c/2` (`paper/main.tex:9594`: "locally bounded by
`C/|x|`"). -/
theorem norm_bsKernel_le_reduced {c : ℝ} (hc : 0 < c) {z : Plane} (hz : |z.1| ≤ c / 2) :
    ‖bsKernel c z‖ ≤ 1 / (2 * c) + 1 / (4 * ‖z‖) := by
  have h1 := norm_bsKernel_sq_le hc hz
  have hB : 0 ≤ 1 / (2 * c) + 1 / (4 * ‖z‖) := by positivity
  have e : (1 / (2 * c) + 1 / (4 * ‖z‖)) ^ 2 =
      1 / (4 * c ^ 2) + 1 / (16 * ‖z‖ ^ 2) + 2 * (1 / (2 * c)) * (1 / (4 * ‖z‖)) := by ring
  have hcross : 0 ≤ 2 * (1 / (2 * c)) * (1 / (4 * ‖z‖)) := by positivity
  have h2 : ‖bsKernel c z‖ ^ 2 ≤ (1 / (2 * c) + 1 / (4 * ‖z‖)) ^ 2 := by
    rw [e]
    linarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hB two_ne_zero).mp h2

/-! ### The near-diagonal majorant -/

/-- Lebesgue measure on the plane is an additive Haar measure (stated for the explicit product, as
in Mathlib's `NumberField` files; instance search does not find it for `ℝ × ℝ`). -/
theorem volume_isAddHaarMeasure : (volume : Measure (ℝ × ℝ)).IsAddHaarMeasure :=
  Measure.prod.instIsAddHaarMeasure _ _

theorem volume_isAddRightInvariant : (volume : Measure (ℝ × ℝ)).IsAddRightInvariant :=
  Measure.prod.instIsAddRightInvariant

/-- The near-diagonal majorant `1_{|w| < 1} |w|^{-1}` (sup norm). -/
def nearKernel (w : Plane) : ℝ := (Metric.ball (0 : Plane) 1).indicator (fun w => ‖w‖⁻¹) w

theorem nearKernel_nonneg (w : Plane) : 0 ≤ nearKernel w := by
  unfold nearKernel
  exact indicator_nonneg (fun _ _ => inv_nonneg.mpr (norm_nonneg _)) w

theorem nearKernel_neg (w : Plane) : nearKernel (-w) = nearKernel w := by
  simp [nearKernel, Set.indicator, norm_neg]

theorem measurable_nearKernel : Measurable nearKernel :=
  (measurable_norm.inv).indicator Metric.isOpen_ball.measurableSet

/-- **Uniformly bounded local `L¹` norm** (`paper/main.tex:9595`): `|w|^{-1}` is integrable on
the unit ball of the plane. -/
theorem integrable_nearKernel : Integrable nearKernel := by
  have := volume_isAddHaarMeasure
  unfold nearKernel
  rw [integrable_indicator_iff Metric.isOpen_ball.measurableSet]
  refine integrableOn_ball_of_norm_le_rpow (μ := volume) (C := 1) (α := 1) (by norm_num)
    (by norm_num) ?_ (measurable_norm.inv).aestronglyMeasurable
  filter_upwards with w
  rw [Real.rpow_neg_one, norm_inv, norm_norm, one_mul]

theorem lintegral_nearKernel_lt_top : ∫⁻ w, ENNReal.ofReal (nearKernel w) < ∞ :=
  integrable_nearKernel.lintegral_lt_top

/-- On the centered strip and for `c ≥ 2`: `‖K_c(w)‖ ≤ 1/2 + nearKernel(w)/4`
(`paper/main.tex:9594–9596`: `C/|x|` near the diagonal, bounded away from it, uniformly in
`c ≥ 2`). -/
theorem norm_bsKernel_le_near {c : ℝ} (hc : 2 ≤ c) {w : Plane} (hw : |w.1| ≤ c / 2) :
    ‖bsKernel c w‖ ≤ 1 / 2 + nearKernel w / 4 := by
  have hc0 : 0 < c := by linarith
  have h1 := norm_bsKernel_le_reduced hc0 hw
  have hc4 : 1 / (2 * c) ≤ 1 / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have h2 : 1 / (4 * ‖w‖) ≤ 1 / 4 + nearKernel w / 4 := by
    by_cases hw1 : ‖w‖ < 1
    · have : nearKernel w = ‖w‖⁻¹ := by
        unfold nearKernel
        rw [indicator_of_mem (by simpa using hw1)]
      rw [this]
      have e : 1 / (4 * ‖w‖) = ‖w‖⁻¹ / 4 := by ring
      rw [e]
      linarith
    · replace hw1 : 1 ≤ ‖w‖ := not_lt.mp hw1
      have : 1 / (4 * ‖w‖) ≤ 1 / 4 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        linarith
      linarith [nearKernel_nonneg w]
  linarith

/-! ### Periodic images seen from a fixed box -/

/-- Number of periodic images: `N = ⌈R/2⌉ + 1`, independent of `c ≥ 2`. -/
def numShifts (R : ℝ) : ℕ := ⌈R / 2⌉₊ + 1

/-- The shifts `j ∈ [-N, N]`. -/
def shifts (R : ℝ) : Finset ℤ := Finset.Icc (-(numShifts R : ℤ)) (numShifts R)

/-- The period vector `(jc, 0)`. -/
def shiftVec (c : ℝ) (j : ℤ) : Plane := ((j : ℝ) * c, 0)

/-- For `x` with `|q| ≤ R`, `y` in the centered cell and `c ≥ 2`:
`‖K_c(x - y)‖ ≤ 1/2 + (1/4) Σ_{|j| ≤ N} nearKernel(x - y - (jc, 0))`. -/
theorem norm_bsKernel_le_sum {c R : ℝ} (hc : 2 ≤ c) {x y : Plane} (hx : |x.1| ≤ R)
    (hy : y ∈ cell c) :
    ‖bsKernel c (x - y)‖ ≤
      1 / 2 + (1 / 4) * ∑ j ∈ shifts R, nearKernel (x - y - shiftVec c j) := by
  have hc0 : 0 < c := by linarith
  have hR : 0 ≤ R := (abs_nonneg _).trans hx
  have hy1 : -(c / 2) ≤ y.1 ∧ y.1 < c / 2 := by
    simpa [cell, mem_prod, mem_Ico] using hy
  have hx1 := abs_le.mp hx
  set t := (x.1 - y.1) / c with ht
  set k : ℤ := round t with hk
  have hkt := abs_le.mp (abs_sub_round t)
  rw [← hk] at hkt
  -- the reduced point `w = x - y - (kc, 0)`
  have ht' : c * t = x.1 - y.1 := by
    rw [ht]
    field_simp
  have hw1 : (x - y - shiftVec c k).1 = c * (t - k) := by
    simp only [shiftVec, Prod.fst_sub]
    linear_combination (-1 : ℝ) * ht'
  have hwK : bsKernel c (x - y) = bsKernel c (x - y - shiftVec c k) := by
    rw [← bsKernel_sub_int hc0.ne' (x - y) k]
    congr 1
    ext <;> simp [shiftVec]
  have hwabs : |(x - y - shiftVec c k).1| ≤ c / 2 := by
    rw [hw1, abs_mul, abs_of_pos hc0]
    have : |t - k| ≤ 1 / 2 := abs_le.mpr ⟨by linarith [hkt.1], by linarith [hkt.2]⟩
    calc c * |t - k| ≤ c * (1 / 2) := mul_le_mul_of_nonneg_left this hc0.le
      _ = c / 2 := by ring
  -- `k` is among the shifts
  have hRc : 0 ≤ R * (c - 2) := mul_nonneg hR (by linarith)
  have htle : t ≤ R / 2 + 1 / 2 := by
    rw [ht, div_le_iff₀ hc0]
    nlinarith
  have htge : -(R / 2 + 1 / 2) ≤ t := by
    rw [ht, le_div_iff₀ hc0]
    nlinarith
  have hceil : R / 2 ≤ (⌈R / 2⌉₊ : ℝ) := Nat.le_ceil _
  have hkmem : k ∈ shifts R := by
    rw [shifts, Finset.mem_Icc, numShifts]
    constructor
    · have : (-(((⌈R / 2⌉₊ + 1 : ℕ) : ℤ)) : ℝ) ≤ (k : ℝ) := by
        push_cast
        linarith [hkt.1, hkt.2]
      exact_mod_cast this
    · have : (k : ℝ) ≤ (((⌈R / 2⌉₊ + 1 : ℕ) : ℤ) : ℝ) := by
        push_cast
        linarith [hkt.1, hkt.2]
      exact_mod_cast this
  have hsum : nearKernel (x - y - shiftVec c k) ≤ ∑ j ∈ shifts R, nearKernel (x - y - shiftVec c j) :=
    Finset.single_le_sum (f := fun j => nearKernel (x - y - shiftVec c j))
      (fun j _ => nearKernel_nonneg _) hkmem
  rw [hwK]
  have := norm_bsKernel_le_near hc hwabs
  linarith

end UnforcedLeray.B0592
