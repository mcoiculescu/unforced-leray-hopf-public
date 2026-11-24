import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Nontangential boundary limits of Cauchy-type integrals (generic part of INF18 O2)

Wave 1 block 1H part 3, scoping note

(bypass B8 (ii): "the nontangential Cauchy limit `I₊` of `∫ W N² /(Ω - c)`"); blueprint unit
B0034 (Lin's continuation, `paper/main.tex` lines 1011--1021).

For a real function `Φ` with a nondegenerate simple zero at `s ∈ (a, b)` (`|Φ t| ≥ m |t - s|`,
`|Φ t - d (t - s)| ≤ K (t - s)²`, `d < 0`) and a Lipschitz `f`, the integral
`∫_a^b f / (Φ - δ)` has a limit as `δ → 0` inside a closed cone `κ |δ| ≤ Im δ` of the upper
half-plane:

* `tendsto_integral_inv_linear`: the model integral `∫_a^b (d (t - s) - δ)⁻¹` tends to
  `(log ((b - s)/(s - a)) - π i)/d` as `δ → 0` with `Im δ > 0` (complex logarithm primitive,
  boundary values of `log` on the cut);
* `tendsto_integral_cauchy_remainder`: the difference `f/(Φ - δ) - f(s)/(d (t - s) - δ)` is
  bounded uniformly in the cone (`norm_ofReal_sub_ge`), so dominated convergence applies;
* `tendsto_integral_cauchy_cone`: the sum.

Mean value tools for the hypotheses: `exists_lipschitz_Icc`, `exists_taylor_two_Icc`,
`mul_abs_sub_le_abs_sub_of_deriv`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory Complex
open scoped Interval ContDiff

namespace UnforcedLeray.ComplexODE

/-- The closed approach cone `κ |δ| ≤ Im δ`, vertex removed. -/
def approachCone (κ : ℝ) : Set ℂ := {δ | κ * ‖δ‖ ≤ δ.im ∧ 0 < δ.im}

theorem approachCone_subset (κ : ℝ) : approachCone κ ⊆ {δ : ℂ | 0 < δ.im} :=
  fun _ hδ => hδ.2

/-- Inside the cone, a real number `A` stays at distance `≥ (min 1 κ / 2) |A|` from `δ`. -/
theorem norm_ofReal_sub_ge {κ : ℝ} (hκ : 0 < κ) {δ : ℂ} (hδ : δ ∈ approachCone κ) (A : ℝ) :
    min 1 κ / 2 * |A| ≤ ‖(A : ℂ) - δ‖ := by
  have hre : |A - δ.re| ≤ ‖(A : ℂ) - δ‖ := by
    have h := Complex.abs_re_le_norm ((A : ℂ) - δ)
    simpa using h
  have him : δ.im ≤ ‖(A : ℂ) - δ‖ := by
    have h := Complex.abs_im_le_norm ((A : ℂ) - δ)
    simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, abs_neg] at h
    exact (le_abs_self _).trans h
  have hδre : |δ.re| ≤ ‖δ‖ := Complex.abs_re_le_norm δ
  have hm1 : min 1 κ * |A| ≤ 1 * |A| :=
    mul_le_mul_of_nonneg_right (min_le_left _ _) (abs_nonneg A)
  have hm2 : min 1 κ * |A| ≤ κ * |A| :=
    mul_le_mul_of_nonneg_right (min_le_right _ _) (abs_nonneg A)
  rcases le_or_gt (|δ.re|) (|A| / 2) with h | h
  · have h1 : |A| - |δ.re| ≤ |A - δ.re| := abs_sub_abs_le_abs_sub A δ.re
    linarith
  · have h1 : κ * |δ.re| ≤ κ * ‖δ‖ := mul_le_mul_of_nonneg_left hδre hκ.le
    have h2 : κ * (|A| / 2) ≤ κ * |δ.re| := mul_le_mul_of_nonneg_left h.le hκ.le
    linarith [hδ.1]

theorem ofReal_sub_ne_zero {δ : ℂ} (hδ : 0 < δ.im) (A : ℝ) : (A : ℂ) - δ ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, Complex.zero_im, neg_eq_zero] at this
  exact hδ.ne' this

theorem ofReal_sub_mem_slitPlane {δ : ℂ} (hδ : 0 < δ.im) (A : ℝ) :
    (A : ℂ) - δ ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  right
  simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, ne_eq, neg_eq_zero]
  exact hδ.ne'

/-- The model Cauchy integral. For `d < 0` and `a < s < b`, as `δ → 0` with `Im δ > 0`,
`∫_a^b (d (t - s) - δ)⁻¹ dt → (log ((b - s)/(s - a)) - π i)/d`. -/
theorem tendsto_integral_inv_linear {a b s d : ℝ} (has : a < s) (hsb : s < b) (hd : d < 0) :
    Tendsto (fun δ : ℂ => ∫ t in a..b, (((d * (t - s) : ℝ) : ℂ) - δ)⁻¹)
      (𝓝[{δ : ℂ | 0 < δ.im}] 0)
      (𝓝 (((Real.log ((b - s) / (s - a)) : ℂ) - Real.pi * I) / d)) := by
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne
  have hint : ∀ δ : ℂ, 0 < δ.im → (∫ t in a..b, (((d * (t - s) : ℝ) : ℂ) - δ)⁻¹) =
      (log (((d * (b - s) : ℝ) : ℂ) - δ) - log (((d * (a - s) : ℝ) : ℂ) - δ)) / d := by
    intro δ hδ
    have hderiv : ∀ t : ℝ, HasDerivAt (fun t : ℝ => log (((d * (t - s) : ℝ) : ℂ) - δ))
        ((d : ℂ) / (((d * (t - s) : ℝ) : ℂ) - δ)) t := by
      intro t
      have h0 : HasDerivAt (fun t : ℝ => d * (t - s)) d t := by
        simpa using ((hasDerivAt_id t).sub_const s).const_mul d
      exact (h0.ofReal_comp.sub_const δ).clog_real (ofReal_sub_mem_slitPlane hδ _)
    have hcont : Continuous (fun t : ℝ => (d : ℂ) / (((d * (t - s) : ℝ) : ℂ) - δ)) := by
      apply continuous_const.div
      · exact (Complex.continuous_ofReal.comp (by fun_prop)).sub continuous_const
      · exact fun t => ofReal_sub_ne_zero hδ _
    have hF := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)
      (hcont.intervalIntegrable a b)
    simp_rw [div_eq_mul_inv (d : ℂ)] at hF
    rw [intervalIntegral.integral_const_mul] at hF
    rw [eq_div_iff hd0, mul_comm, hF]
  have hbneg : d * (b - s) < 0 := mul_neg_of_neg_of_pos hd (by linarith)
  have hapos : 0 < d * (a - s) := mul_pos_of_neg_of_neg hd (by linarith)
  have hlim_b : Tendsto (fun δ : ℂ => log (((d * (b - s) : ℝ) : ℂ) - δ))
      (𝓝[{δ : ℂ | 0 < δ.im}] 0)
      (𝓝 (Real.log ‖((d * (b - s) : ℝ) : ℂ)‖ - Real.pi * I)) := by
    apply (tendsto_log_nhdsWithin_im_neg_of_re_neg_of_im_zero
      (by simpa using hbneg) (by simp)).comp
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have h : Tendsto (fun δ : ℂ => ((d * (b - s) : ℝ) : ℂ) - δ) (𝓝 0)
          (𝓝 (((d * (b - s) : ℝ) : ℂ) - 0)) := tendsto_const_nhds.sub tendsto_id
      rw [sub_zero] at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with δ hδ
      simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, neg_lt_zero]
      exact hδ
  have hlim_a : Tendsto (fun δ : ℂ => log (((d * (a - s) : ℝ) : ℂ) - δ))
      (𝓝[{δ : ℂ | 0 < δ.im}] 0) (𝓝 (log ((d * (a - s) : ℝ) : ℂ))) := by
    have hc := continuousAt_clog (ofReal_mem_slitPlane.2 hapos)
    have h : Tendsto (fun δ : ℂ => ((d * (a - s) : ℝ) : ℂ) - δ) (𝓝 0)
        (𝓝 (((d * (a - s) : ℝ) : ℂ) - 0)) := tendsto_const_nhds.sub tendsto_id
    rw [sub_zero] at h
    exact (hc.tendsto.comp h).mono_left nhdsWithin_le_nhds
  have hval : ((Real.log ‖((d * (b - s) : ℝ) : ℂ)‖ : ℂ) - Real.pi * I -
      log ((d * (a - s) : ℝ) : ℂ)) / d =
      (((Real.log ((b - s) / (s - a)) : ℂ) - Real.pi * I) / d) := by
    rw [← ofReal_log hapos.le, Complex.norm_real, Real.norm_eq_abs, abs_of_neg hbneg]
    have hl : Real.log (-(d * (b - s))) - Real.log (d * (a - s)) =
        Real.log ((b - s) / (s - a)) := by
      rw [show -(d * (b - s)) = (-d) * (b - s) by ring,
        show d * (a - s) = (-d) * (s - a) by ring,
        Real.log_mul (by linarith) (by linarith), Real.log_mul (by linarith) (by linarith),
        Real.log_div (by linarith) (by linarith)]
      ring
    rw [← hl]
    push_cast
    ring
  rw [← hval]
  apply ((hlim_b.sub hlim_a).div_const (d : ℂ)).congr'
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact (hint δ hδ).symm

/-- **Dominated remainder.** Let `Φ, f` be continuous, `d ≠ 0`, and on `[a, b]`:
`m |t - s| ≤ |Φ t|`, `|f t - f s| ≤ L |t - s|`, `|Φ t - d (t - s)| ≤ K (t - s)²`. Then, as
`δ → 0` in the cone, `∫_a^b (f/(Φ - δ) - f(s)/(d (t - s) - δ))` tends to the absolutely
convergent real integral `∫_a^b (f/Φ - f(s)/(d (t - s)))`. -/
theorem tendsto_integral_cauchy_remainder {a b s d m L K κ : ℝ} {Φ f : ℝ → ℝ}
    (hab : a ≤ b) (hκ : 0 < κ) (hd : d ≠ 0) (hm : 0 < m) (hL : 0 ≤ L) (hK : 0 ≤ K)
    (hΦc : Continuous Φ) (hfc : Continuous f)
    (h1 : ∀ t ∈ Icc a b, m * |t - s| ≤ |Φ t|)
    (h2 : ∀ t ∈ Icc a b, |f t - f s| ≤ L * |t - s|)
    (h3 : ∀ t ∈ Icc a b, |Φ t - d * (t - s)| ≤ K * (t - s) ^ 2) :
    Tendsto (fun δ : ℂ => ∫ t in a..b,
        ((f t : ℂ) / ((Φ t : ℂ) - δ) - (f s : ℂ) / (((d * (t - s) : ℝ) : ℂ) - δ)))
      (𝓝[approachCone κ] 0)
      (𝓝 (((∫ t in a..b, (f t / Φ t - f s / (d * (t - s)))) : ℝ) : ℂ)) := by
  set c₁ : ℝ := min 1 κ / 2 with hc₁
  have hc₁0 : 0 < c₁ := by rw [hc₁]; exact half_pos (lt_min one_pos hκ)
  set C₁ : ℝ := L / (c₁ * m) with hC₁
  set C₂ : ℝ := |f s| * K / (c₁ * m * (c₁ * |d|)) with hC₂
  have hdabs : 0 < |d| := abs_pos.mpr hd
  have hC₁0 : 0 ≤ C₁ := div_nonneg hL (by positivity)
  have hC₂0 : 0 ≤ C₂ := div_nonneg (mul_nonneg (abs_nonneg _) hK) (by positivity)
  rw [← intervalIntegral.integral_ofReal]
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => C₁ + C₂)
    ?_ ?_ intervalIntegrable_const ?_
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    apply Continuous.aestronglyMeasurable
    apply Continuous.sub
    · exact (Complex.continuous_ofReal.comp hfc).div
        ((Complex.continuous_ofReal.comp hΦc).sub continuous_const)
        (fun t => ofReal_sub_ne_zero hδ.2 _)
    · exact continuous_const.div
        ((Complex.continuous_ofReal.comp (by fun_prop)).sub continuous_const)
        (fun t => ofReal_sub_ne_zero hδ.2 _)
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    filter_upwards [(volume : Measure ℝ).ae_ne s] with t hts ht
    have htI : t ∈ Icc a b := by
      rw [uIoc_of_le hab] at ht
      exact ⟨ht.1.le, ht.2⟩
    set A : ℝ := Φ t with hA
    set B : ℝ := d * (t - s) with hB
    have he : 0 < |t - s| := abs_pos.mpr (sub_ne_zero.mpr hts)
    have hAδ : c₁ * m * |t - s| ≤ ‖(A : ℂ) - δ‖ := by
      have := norm_ofReal_sub_ge hκ hδ A
      have hA1 := h1 t htI
      calc c₁ * m * |t - s| = c₁ * (m * |t - s|) := by ring
        _ ≤ c₁ * |A| := mul_le_mul_of_nonneg_left hA1 hc₁0.le
        _ ≤ _ := this
    have hBδ : c₁ * |d| * |t - s| ≤ ‖(B : ℂ) - δ‖ := by
      have := norm_ofReal_sub_ge hκ hδ B
      rw [hB, abs_mul] at this
      calc c₁ * |d| * |t - s| = c₁ * (|d| * |t - s|) := by ring
        _ ≤ _ := this
    have hApos : 0 < ‖(A : ℂ) - δ‖ := lt_of_lt_of_le (by positivity) hAδ
    have hBpos : 0 < ‖(B : ℂ) - δ‖ := lt_of_lt_of_le (by positivity) hBδ
    have hA0 : (A : ℂ) - δ ≠ 0 := norm_pos_iff.mp hApos
    have hB0 : (B : ℂ) - δ ≠ 0 := norm_pos_iff.mp hBpos
    have hid : (f t : ℂ) / ((A : ℂ) - δ) - (f s : ℂ) / ((B : ℂ) - δ) =
        ((f t - f s : ℝ) : ℂ) / ((A : ℂ) - δ) +
          (f s : ℂ) * ((B - A : ℝ) : ℂ) / (((A : ℂ) - δ) * ((B : ℂ) - δ)) := by
      push_cast
      field_simp
      ring
    rw [hid]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_div, Complex.norm_real, Real.norm_eq_abs, div_le_iff₀ hApos]
      calc |f t - f s| ≤ L * |t - s| := h2 t htI
        _ = C₁ * (c₁ * m * |t - s|) := by
          rw [hC₁]; field_simp
        _ ≤ C₁ * ‖(A : ℂ) - δ‖ := mul_le_mul_of_nonneg_left hAδ hC₁0
    · rw [norm_div, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, div_le_iff₀ (mul_pos hApos hBpos)]
      have hBA : |B - A| ≤ K * |t - s| ^ 2 := by
        rw [abs_sub_comm, sq_abs]
        exact h3 t htI
      calc |f s| * |B - A| ≤ |f s| * (K * |t - s| ^ 2) :=
            mul_le_mul_of_nonneg_left hBA (abs_nonneg _)
        _ = C₂ * ((c₁ * m * |t - s|) * (c₁ * |d| * |t - s|)) := by
          rw [hC₂]; field_simp
        _ ≤ C₂ * (‖(A : ℂ) - δ‖ * ‖(B : ℂ) - δ‖) :=
            mul_le_mul_of_nonneg_left (mul_le_mul hAδ hBδ (by positivity) hApos.le) hC₂0
  · filter_upwards [(volume : Measure ℝ).ae_ne s] with t hts ht
    have htI : t ∈ Icc a b := by
      rw [uIoc_of_le hab] at ht
      exact ⟨ht.1.le, ht.2⟩
    have he : 0 < |t - s| := abs_pos.mpr (sub_ne_zero.mpr hts)
    have hΦ0 : Φ t ≠ 0 := by
      have := h1 t htI
      exact abs_pos.mp (lt_of_lt_of_le (mul_pos hm he) this)
    have hB0 : d * (t - s) ≠ 0 := mul_ne_zero hd (sub_ne_zero.mpr hts)
    have hcont : ContinuousAt (fun δ : ℂ =>
        (f t : ℂ) / ((Φ t : ℂ) - δ) - (f s : ℂ) / (((d * (t - s) : ℝ) : ℂ) - δ)) 0 := by
      apply ContinuousAt.sub
      · exact continuousAt_const.div (continuousAt_const.sub continuousAt_id)
          (by simpa using hΦ0)
      · exact continuousAt_const.div (continuousAt_const.sub continuousAt_id)
          (by rw [sub_zero]; exact_mod_cast hB0)
    have h := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := approachCone κ))
    convert h using 2
    push_cast
    simp

/-- **Nontangential Cauchy limit.** Under the hypotheses of
`tendsto_integral_cauchy_remainder`, with `d < 0` and `a < s < b`,
`∫_a^b f/(Φ - δ) → ∫_a^b (f/Φ - f(s)/(d (t - s))) + f(s) (log ((b - s)/(s - a)) - π i)/d`
as `δ → 0` in the cone `κ |δ| ≤ Im δ`. -/
theorem tendsto_integral_cauchy_cone {a b s d m L K κ : ℝ} {Φ f : ℝ → ℝ}
    (has : a < s) (hsb : s < b) (hκ : 0 < κ) (hd : d < 0) (hm : 0 < m) (hL : 0 ≤ L)
    (hK : 0 ≤ K) (hΦc : Continuous Φ) (hfc : Continuous f)
    (h1 : ∀ t ∈ Icc a b, m * |t - s| ≤ |Φ t|)
    (h2 : ∀ t ∈ Icc a b, |f t - f s| ≤ L * |t - s|)
    (h3 : ∀ t ∈ Icc a b, |Φ t - d * (t - s)| ≤ K * (t - s) ^ 2) :
    Tendsto (fun δ : ℂ => ∫ t in a..b, (f t : ℂ) / ((Φ t : ℂ) - δ)) (𝓝[approachCone κ] 0)
      (𝓝 ((((∫ t in a..b, (f t / Φ t - f s / (d * (t - s)))) : ℝ) : ℂ) +
        (f s : ℂ) * (((Real.log ((b - s) / (s - a)) : ℂ) - Real.pi * I) / d))) := by
  have hab : a ≤ b := (has.trans hsb).le
  have hR := tendsto_integral_cauchy_remainder hab hκ hd.ne hm hL hK hΦc hfc h1 h2 h3
  have hM := ((tendsto_integral_inv_linear has hsb hd).mono_left
    (nhdsWithin_mono _ (approachCone_subset κ))).const_mul (f s : ℂ)
  apply (hR.add hM).congr'
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  have hcR : Continuous (fun t : ℝ =>
      (f t : ℂ) / ((Φ t : ℂ) - δ) - (f s : ℂ) / (((d * (t - s) : ℝ) : ℂ) - δ)) := by
    apply Continuous.sub
    · exact (Complex.continuous_ofReal.comp hfc).div
        ((Complex.continuous_ofReal.comp hΦc).sub continuous_const)
        (fun t => ofReal_sub_ne_zero hδ.2 _)
    · exact continuous_const.div
        ((Complex.continuous_ofReal.comp (by fun_prop)).sub continuous_const)
        (fun t => ofReal_sub_ne_zero hδ.2 _)
  have hcM : Continuous (fun t : ℝ => (((d * (t - s) : ℝ) : ℂ) - δ)⁻¹) :=
    ((Complex.continuous_ofReal.comp (by fun_prop)).sub continuous_const).inv₀
      (fun t => ofReal_sub_ne_zero hδ.2 _)
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add
    (f := fun t : ℝ => (f t : ℂ) / ((Φ t : ℂ) - δ) - (f s : ℂ) / (((d * (t - s) : ℝ) : ℂ) - δ))
    (g := fun t : ℝ => (f s : ℂ) * (((d * (t - s) : ℝ) : ℂ) - δ)⁻¹)
    (hcR.intervalIntegrable a b) ((continuous_const.mul hcM).intervalIntegrable a b)]
  apply intervalIntegral.integral_congr
  intro t _
  simp only [div_eq_mul_inv]
  ring

/-! ### Mean value tools -/

/-- A `C¹` function is Lipschitz on a compact interval. -/
theorem exists_lipschitz_Icc {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F) (a b : ℝ) :
    ∃ L ≥ 0, ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, |F y - F x| ≤ L * |y - x| := by
  obtain ⟨L, hL⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hF.continuous_deriv le_rfl).continuousOn (s := Icc a b)
  refine ⟨max L 0, le_max_right _ _, fun x hx y hy => ?_⟩
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := F) (f' := deriv F)
    (fun z _ => ((hF.differentiable one_ne_zero) z).hasDerivAt.hasDerivWithinAt)
    (C := max L 0) (fun z hz => (hL z hz).trans (le_max_left L 0)) (convex_Icc a b) hx hy
  simpa only [Real.norm_eq_abs] using h

/-- Second-order Taylor bound on a compact interval for a smooth function. -/
theorem exists_taylor_two_Icc {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (a b : ℝ) :
    ∃ K ≥ 0, ∀ x ∈ Icc a b, ∀ y ∈ Icc a b,
      |F y - F x - deriv F x * (y - x)| ≤ K * (y - x) ^ 2 := by
  have hF' : ContDiff ℝ 1 (deriv F) := by
    have h := (contDiff_infty_iff_deriv.mp hF).2
    exact_mod_cast contDiff_infty.mp h 1
  obtain ⟨K, hK, hKL⟩ := exists_lipschitz_Icc hF' a b
  refine ⟨K, hK, fun x hx y hy => ?_⟩
  have hseg : uIcc x y ⊆ Icc a b := uIcc_subset_Icc hx hy
  have hd : ∀ z, HasDerivAt (fun z => F z - F x - deriv F x * (z - x)) (deriv F z - deriv F x) z := by
    intro z
    have h1 := ((hF.differentiable (by simp)) z).hasDerivAt
    have h2 : HasDerivAt (fun z => deriv F x * (z - x)) (deriv F x) z := by
      simpa using ((hasDerivAt_id' z).sub_const x).const_mul (deriv F x)
    exact (h1.sub_const (F x)).sub h2
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun z => F z - F x - deriv F x * (z - x)) (f' := fun z => deriv F z - deriv F x)
    (C := K * |y - x|) (fun z _ => (hd z).hasDerivWithinAt)
    (fun z hz => by
      rw [Real.norm_eq_abs]
      refine (hKL x hx z (hseg hz)).trans (mul_le_mul_of_nonneg_left ?_ hK)
      exact abs_sub_left_of_mem_uIcc hz)
    (convex_uIcc x y) (left_mem_uIcc) (right_mem_uIcc)
  simp only [sub_self, mul_zero, sub_zero, Real.norm_eq_abs] at h
  calc |F y - F x - deriv F x * (y - x)| ≤ K * |y - x| * |y - x| := h
    _ = K * (y - x) ^ 2 := by rw [mul_assoc, ← sq, sq_abs]

/-- A derivative bounded below in absolute value gives a two-sided distance bound. -/
theorem mul_abs_sub_le_abs_sub_of_deriv {F F' : ℝ → ℝ} {a b m : ℝ}
    (hF : ∀ x, HasDerivAt F (F' x) x) (hm : ∀ x ∈ Icc a b, m ≤ |F' x|) :
    ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, m * |y - x| ≤ |F y - F x| := by
  have hFc : Continuous F := continuous_iff_continuousAt.2 fun x => (hF x).continuousAt
  have key : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, x < y → m * |y - x| ≤ |F y - F x| := by
    intro x hx y hy hxy
    obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope F F' hxy hFc.continuousOn
      (fun z _ => hF z)
    have hξI : ξ ∈ Icc a b := ⟨hx.1.trans hξ.1.le, hξ.2.le.trans hy.2⟩
    have hyx : 0 < y - x := sub_pos.mpr hxy
    have heq : F y - F x = F' ξ * (y - x) := by
      rw [hξeq]; field_simp
    rw [heq, abs_mul, abs_of_pos hyx]
    exact mul_le_mul_of_nonneg_right (hm ξ hξI) hyx.le
  intro x hx y hy
  rcases lt_trichotomy x y with h | h | h
  · exact key x hx y hy h
  · subst h; simp
  · rw [abs_sub_comm y x, abs_sub_comm (F y) (F x)]
    exact key y hy x hx h

end UnforcedLeray.ComplexODE
