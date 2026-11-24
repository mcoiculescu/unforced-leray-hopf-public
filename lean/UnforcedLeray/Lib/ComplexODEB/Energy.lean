import UnforcedLeray.Lib.ComplexODEB.Cauchy
import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# B0034 helper: second-derivative bound without `1/Im c` at any angular index

*Provenance (Wave 2 block 2H PLAN1b).* Copy of the compiled draft

`Lib/ComplexODE` (the copies `Lib/ComplexODE/NeutralSolution` and `Lib/ComplexODE/L1Dependence`
replace the drafts `Analysis/Rayleigh/Evans/NeutralSolution` and `L1ContinuousGronwall`), with
namespace `UnforcedLeray.ComplexODEB` in place of `UnforcedLeray.B0034`. Do not import it
together with `Units/B0034` helpers that pull in those drafts.

Step of the continuation behind B0034 (`paper/main.tex`, eq. `st18-t00034`–`st18-t00036`,
lines 1029–1048, used at a real wavenumber `β` as in Lin 2003, Lemma 5.8; whole-line
analogue (3.3)–(3.5) of the Lin-free route, commit 4dd0a82). For a Dirichlet solution
`F = normalizedF β a c` on `[a, b]` (`evansFunction β a b c = 0`, `Im c > 0`),

`∫ |F''|² ≤ (2 β⁴ + 128) ∫ |F|²`  (`energy_bound`).

Proof. Integration by parts makes `∫ F'' F̄` real, so with `q = A/(Ω - c) = -W J/(J - z)`
(`J = Ω - a_*`, `z = c - a_*`) and `w = W|F|²/|J - z|²`: `∫ J w = 0`. Then
`J² w = W|F|² + (2 J Re z - |z|²) w` gives `∫ J² w ≤ ∫ W|F|² ≤ 8 ∫|F|²`, and
`|q|²|F|² = W J² w ≤ 8 J² w`.
-/

set_option autoImplicit false

noncomputable section
open Set Filter Topology MeasureTheory Complex
namespace UnforcedLeray.ComplexODEB
open UnforcedLeray.Rayleigh UnforcedLeray.Rayleigh.Evans UnforcedLeray.Sturm
open UnforcedLeray.GaussianPotential

/-- Integration by parts: `∫ F'' F̄` is real for Dirichlet data. -/
theorem im_integral_deriv2_mul_star {a b : ℝ} {F F' F'' : ℝ → ℂ}
    (hF : ∀ t, HasDerivAt F (F' t) t) (hF' : ∀ t, HasDerivAt F' (F'' t) t)
    (hF''c : Continuous F'') (ha : F a = 0) (hb : F b = 0) :
    (∫ t in a..b, F'' t * star (F t)).im = 0 := by
  have hFc : Continuous F := continuous_iff_continuousAt.mpr fun t => (hF t).continuousAt
  have hF'c : Continuous F' := continuous_iff_continuousAt.mpr fun t => (hF' t).continuousAt
  have hd : ∀ t ∈ uIcc a b, HasDerivAt (fun s => F' s * star (F s))
      (F'' t * star (F t) + F' t * star (F' t)) t := fun t _ =>
    (hF' t).mul (hF t).star
  have hc : Continuous (fun t => F'' t * star (F t) + F' t * star (F' t)) :=
    (hF''c.mul hFc.star).add (hF'c.mul hF'c.star)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable a b)
  rw [ha, hb, star_zero, mul_zero, mul_zero, sub_zero] at hftc
  have i1 : IntervalIntegrable (fun t => F'' t * star (F t)) volume a b :=
    (hF''c.mul hFc.star).intervalIntegrable a b
  have i2 : IntervalIntegrable (fun t => F' t * star (F' t)) volume a b :=
    (hF'c.mul hF'c.star).intervalIntegrable a b
  rw [intervalIntegral.integral_add i1 i2] at hftc
  have hreal : (∫ t in a..b, F' t * star (F' t)) = ((∫ t in a..b, ‖F' t‖ ^ 2 : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr
    intro t _
    simp only [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have : (∫ t in a..b, F'' t * star (F t)) = -((∫ t in a..b, ‖F' t‖ ^ 2 : ℝ) : ℂ) := by
    rw [← hreal]
    linear_combination hftc
  rw [this]
  simp

/-- The imaginary part of an interval integral. -/
theorem im_intervalIntegral {a b : ℝ} {f : ℝ → ℂ} (hf : Continuous f) :
    (∫ t in a..b, f t).im = ∫ t in a..b, (f t).im := by
  have h := Complex.imCLM.intervalIntegral_comp_comm (hf.intervalIntegrable (μ := volume) a b)
  simp only [Complex.imCLM_apply] at h
  exact h.symm

/-- The uniform second-derivative bound for a Dirichlet solution. -/
theorem energy_bound {a b β : ℝ} (hab : a ≤ b) {c : ℂ} (hc : 0 < c.im)
    (hz : evansFunction β a b c = 0) :
    (∫ t in a..b, ‖rayleighPotential β t c * normalizedF β a c t‖ ^ 2) ≤
      (2 * β ^ 4 + 128) * ∫ t in a..b, ‖normalizedF β a c t‖ ^ 2 := by
  set F := normalizedF β a c with hF
  set z : ℂ := c - (gaussianCriticalSpeed : ℂ) with hzdef
  have hzim : 0 < z.im := by rw [hzdef]; simpa using hc
  have hFc : Continuous F := (normalizedF_smooth β a hc).continuous
  have hVc : Continuous (fun t => rayleighPotential β t c) := continuous_rayleighPotential β hc
  have hden : ∀ t, (gaussianOffset t : ℂ) - z ≠ 0 := fun t => criticalDenominator_ne_zero _ hzim
  have hdenpos : ∀ t, 0 < ‖(gaussianOffset t : ℂ) - z‖ := fun t => norm_pos_iff.mpr (hden t)
  have hdeneq : ∀ t, (neutralOmega t : ℂ) - c = (gaussianOffset t : ℂ) - z := fun t => by
    rw [hzdef]; simp [gaussianOffset]
  -- the quotient `q = A/(Ω - c) = -W J/(J - z)`
  have hq : ∀ t, rayleighPotential β t c =
      (β : ℂ) ^ 2 - (Wlog t : ℂ) * (gaussianOffset t : ℂ) / ((gaussianOffset t : ℂ) - z) := by
    intro t
    unfold rayleighPotential gaussianRayleighCoefficient
    rw [hdeneq]
    push_cast
    ring
  -- the weight `w`
  set w : ℝ → ℝ := fun t => Wlog t * ‖F t‖ ^ 2 / ‖(gaussianOffset t : ℂ) - z‖ ^ 2 with hw
  have hdenc : Continuous (fun t => ‖(gaussianOffset t : ℂ) - z‖ ^ 2) :=
    ((Complex.continuous_ofReal.comp continuous_gaussianOffset').sub continuous_const).norm.pow 2
  have hwc : Continuous w :=
    (continuous_Wlog.mul (hFc.norm.pow 2)).div hdenc (fun t => (pow_pos (hdenpos t) 2).ne')
  have hw0 : ∀ t, 0 ≤ w t := fun t =>
    div_nonneg (mul_nonneg (Wlog_pos t).le (sq_nonneg _)) (sq_nonneg _)
  -- Step 1: `∫ J w = 0`
  have hdF : ∀ t, HasDerivAt F (normalizedDerivative β a c t) t := hasDerivAt_normalizedF β a hc
  have hdF' : ∀ t, HasDerivAt (normalizedDerivative β a c)
      (rayleighPotential β t c * F t) t := hasDerivAt_normalizedDerivative β a hc
  have him := im_integral_deriv2_mul_star hdF hdF' (hVc.mul hFc)
    (normalizedF_initial β a hc) hz
  have hVFc : Continuous (fun t => rayleighPotential β t c * F t * star (F t)) :=
    (hVc.mul hFc).mul hFc.star
  rw [im_intervalIntegral hVFc] at him
  have key : ∀ t, (rayleighPotential β t c).im =
      -(Wlog t * gaussianOffset t * z.im / ‖(gaussianOffset t : ℂ) - z‖ ^ 2) := by
    intro t
    rw [hq, Complex.sub_im, ← Complex.ofReal_pow, Complex.ofReal_im, ← Complex.ofReal_mul,
      Complex.div_im, Complex.ofReal_im, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    simp only [Complex.sub_im, Complex.ofReal_im]
    ring
  have hpt : ∀ t, (rayleighPotential β t c * F t * star (F t)).im =
      -(z.im * (gaussianOffset t * w t)) := by
    intro t
    rw [mul_assoc, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    simp only [Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, mul_zero, zero_add]
    rw [key]
    simp only [hw]
    have hd := hdenpos t
    field_simp
  have hJw : (∫ t in a..b, gaussianOffset t * w t) = 0 := by
    have h1 : (∫ t in a..b, (rayleighPotential β t c * F t * star (F t)).im) =
        -(z.im * ∫ t in a..b, gaussianOffset t * w t) := by
      rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_neg]
      exact intervalIntegral.integral_congr (fun t _ => hpt t)
    rw [h1] at him
    have := neg_eq_zero.mp him
    exact (mul_eq_zero.mp this).resolve_left hzim.ne'
  -- Step 2: `∫ J² w ≤ ∫ W |F|² ≤ 8 ∫ |F|²`
  have hJ2 : ∀ t, gaussianOffset t ^ 2 * w t =
      Wlog t * ‖F t‖ ^ 2 + (2 * gaussianOffset t * z.re - ‖z‖ ^ 2) * w t := by
    intro t
    have hn : ‖(gaussianOffset t : ℂ) - z‖ ^ 2 =
        gaussianOffset t ^ 2 - 2 * gaussianOffset t * z.re + ‖z‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
        Complex.normSq_apply]
      simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im]
      ring
    simp only [hw]
    have hD0 : ‖(gaussianOffset t : ℂ) - z‖ ^ 2 ≠ 0 := (pow_pos (hdenpos t) 2).ne'
    generalize hD : ‖(gaussianOffset t : ℂ) - z‖ ^ 2 = D at hn hD0 ⊢
    field_simp
    rw [hn]
    ring
  have hJc : Continuous gaussianOffset := continuous_gaussianOffset'
  have j1 : IntervalIntegrable (fun t => Wlog t * ‖F t‖ ^ 2) volume a b :=
    (continuous_Wlog.mul (hFc.norm.pow 2)).intervalIntegrable a b
  have j2 : IntervalIntegrable (fun t => gaussianOffset t * w t) volume a b :=
    (hJc.mul hwc).intervalIntegrable a b
  have j3 : IntervalIntegrable w volume a b := hwc.intervalIntegrable a b
  have hint2 : (∫ t in a..b, gaussianOffset t ^ 2 * w t) =
      (∫ t in a..b, Wlog t * ‖F t‖ ^ 2) + 2 * z.re * (∫ t in a..b, gaussianOffset t * w t) -
        ‖z‖ ^ 2 * ∫ t in a..b, w t := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add j1 (j2.const_mul _),
      ← intervalIntegral.integral_sub (j1.add (j2.const_mul _)) (j3.const_mul _)]
    apply intervalIntegral.integral_congr
    intro t _
    simp only
    rw [hJ2]
    ring
  have hwint : 0 ≤ ∫ t in a..b, w t := intervalIntegral.integral_nonneg hab (fun t _ => hw0 t)
  have hWF : (∫ t in a..b, Wlog t * ‖F t‖ ^ 2) ≤ 8 * ∫ t in a..b, ‖F t‖ ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hab j1 ((hFc.norm.pow 2).intervalIntegrable a b
      |>.const_mul 8)
    intro t _
    exact mul_le_mul_of_nonneg_right (Wlog_le_eight t) (sq_nonneg _)
  have hJ2le : (∫ t in a..b, gaussianOffset t ^ 2 * w t) ≤ 8 * ∫ t in a..b, ‖F t‖ ^ 2 := by
    rw [hint2, hJw]
    nlinarith [mul_nonneg (sq_nonneg ‖z‖) hwint]
  -- Step 3: the pointwise bound
  have hptb : ∀ t, ‖rayleighPotential β t c * F t‖ ^ 2 ≤
      2 * β ^ 4 * ‖F t‖ ^ 2 + 16 * (gaussianOffset t ^ 2 * w t) := by
    intro t
    rw [hq, sub_mul]
    have h1 : ‖(β : ℂ) ^ 2 * F t‖ = β ^ 2 * ‖F t‖ := by
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    have h2 : ‖(Wlog t : ℂ) * (gaussianOffset t : ℂ) / ((gaussianOffset t : ℂ) - z) * F t‖ ^ 2 =
        Wlog t * (gaussianOffset t ^ 2 * w t) := by
      simp only [hw]
      rw [norm_mul, norm_div, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_pos (Wlog_pos t)]
      have hd := hdenpos t
      field_simp
      rw [sq_abs]
      ring
    have hsq : ∀ x y : ℂ, ‖x - y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := fun x y => by
      have := norm_sub_le x y
      nlinarith [sq_nonneg (‖x‖ - ‖y‖), norm_nonneg (x - y)]
    refine (hsq _ _).trans ?_
    rw [h1, h2]
    have hW := Wlog_le_eight t
    have hJw0 : 0 ≤ gaussianOffset t ^ 2 * w t := mul_nonneg (sq_nonneg _) (hw0 t)
    nlinarith [mul_le_mul_of_nonneg_right hW hJw0]
  -- Step 4: integrate
  have j4 : IntervalIntegrable (fun t => 2 * β ^ 4 * ‖F t‖ ^ 2 + 16 * (gaussianOffset t ^ 2 * w t))
      volume a b :=
    ((continuous_const.mul (hFc.norm.pow 2)).add
      (continuous_const.mul ((hJc.pow 2).mul hwc))).intervalIntegrable a b
  calc (∫ t in a..b, ‖rayleighPotential β t c * F t‖ ^ 2)
      ≤ ∫ t in a..b, (2 * β ^ 4 * ‖F t‖ ^ 2 + 16 * (gaussianOffset t ^ 2 * w t)) :=
        intervalIntegral.integral_mono_on hab (((hVc.mul hFc).norm.pow 2).intervalIntegrable a b)
          j4 (fun t _ => hptb t)
    _ = 2 * β ^ 4 * (∫ t in a..b, ‖F t‖ ^ 2) + 16 * ∫ t in a..b, gaussianOffset t ^ 2 * w t := by
        have k1 : IntervalIntegrable (fun t => 2 * β ^ 4 * ‖F t‖ ^ 2) volume a b :=
          ((hFc.norm.pow 2).intervalIntegrable a b).const_mul _
        have k2 : IntervalIntegrable (fun t => 16 * (gaussianOffset t ^ 2 * w t)) volume a b :=
          ((((hJc.pow 2).mul hwc).intervalIntegrable a b).const_mul _)
        rw [intervalIntegral.integral_add k1 k2,
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    _ ≤ (2 * β ^ 4 + 128) * ∫ t in a..b, ‖F t‖ ^ 2 := by nlinarith

end UnforcedLeray.ComplexODEB
