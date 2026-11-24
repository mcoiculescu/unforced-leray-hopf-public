import UnforcedLeray.Lib.ComplexODE.CriticalCauchy
import UnforcedLeray.Lib.ComplexODE.QuantitativeL1
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Logarithmic L¹ bound for the Rayleigh critical kernel (INF18 O3 supplement)

Wave 1 block 1H part 3, scoping note

and §6 risk 2: the L¹ dependence is used in the form
`sup |F - N| ≤ C (|α² - β²| + |z| log(1/Im z))`, which needs
`∫_a^b W/|Ω - c| ≤ C (1 + log (1/Im c))` uniformly in `Re c` (`paper/main.tex` lines 1011--1021,
blueprint unit B0034).

* `integral_inv_abs_add` (generalizing the draft `CauchyKernelBound.integral_abs_add_inv` of

  center on the closed interval): `∫_a^b (|t - τ| + ε)⁻¹ = log ((τ - a + ε)/ε) + log ((b - τ + ε)/ε)`;
* `exists_integral_Wlog_div_norm_le_log`: for `0 < Im c ≤ 1`,
  `∫_a^b W/|Ω - c| ≤ C (1 + log (1/Im c))`, with `C` depending on `[a, b]` only. The real part
  of `c` is arbitrary: since `Ω` is monotone with `|Ω'| ≥ m > 0` on `[a, b]`, there is always
  `τ ∈ [a, b]` with `|Ω t - Re c| ≥ m |t - τ|`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory Complex
open scoped Interval

namespace UnforcedLeray.ComplexODE

theorem continuous_inv_abs_add {ε : ℝ} (hε : 0 < ε) (τ : ℝ) :
    Continuous (fun t : ℝ => (|t - τ| + ε)⁻¹) :=
  (((continuous_id.sub continuous_const).abs).add continuous_const).inv₀
    (fun t => (by positivity : (0 : ℝ) < |t - τ| + ε).ne')

/-- The comparison kernel has an exact logarithmic integral, for a center on `[a, b]`. -/
theorem integral_inv_abs_add {a b τ ε : ℝ} (haτ : a ≤ τ) (hτb : τ ≤ b) (hε : 0 < ε) :
    (∫ t in a..b, (|t - τ| + ε)⁻¹) =
      Real.log ((τ - a + ε) / ε) + Real.log ((b - τ + ε) / ε) := by
  have hleft : (∫ t in a..τ, (|t - τ| + ε)⁻¹) = Real.log ((τ - a + ε) / ε) := by
    calc
      _ = ∫ t in a..τ, ((τ + ε) - t)⁻¹ := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le haτ] at ht
        simp only
        rw [abs_of_nonpos (sub_nonpos.mpr ht.2)]
        congr 1
        ring
      _ = ∫ t in ε..(τ - a + ε), t⁻¹ := by
        rw [intervalIntegral.integral_comp_sub_left (fun t => t⁻¹)]
        congr 1 <;> ring
      _ = _ := integral_inv_of_pos hε (by linarith)
  have hright : (∫ t in τ..b, (|t - τ| + ε)⁻¹) = Real.log ((b - τ + ε) / ε) := by
    calc
      _ = ∫ t in τ..b, (t + (ε - τ))⁻¹ := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hτb] at ht
        simp only
        rw [abs_of_nonneg (sub_nonneg.mpr ht.1)]
        congr 1
        ring
      _ = ∫ t in ε..(b - τ + ε), t⁻¹ := by
        rw [intervalIntegral.integral_comp_add_right (fun t => t⁻¹)]
        congr 1 <;> ring
      _ = _ := integral_inv_of_pos hε (by linarith)
  rw [← intervalIntegral.integral_add_adjacent_intervals
    ((continuous_inv_abs_add hε τ).intervalIntegrable a τ)
    ((continuous_inv_abs_add hε τ).intervalIntegrable τ b), hleft, hright]

/-- `log ((ℓ + ε')/ε') ≤ log (1 + ℓ m) + log (1/ε)` for `ε' = ε/m`, `0 < ε ≤ 1`, `0 ≤ ℓ`. -/
theorem log_ratio_le {ℓ m ε : ℝ} (hℓ : 0 ≤ ℓ) (hm : 0 < m) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    Real.log ((ℓ + ε / m) / (ε / m)) ≤ Real.log (1 + ℓ * m) + Real.log (1 / ε) := by
  have hεm : 0 < ε / m := div_pos hε hm
  have hq : (ℓ + ε / m) / (ε / m) = 1 + ℓ * m / ε := by
    field_simp
    ring
  rw [hq, ← Real.log_mul (by positivity) (by positivity)]
  apply Real.log_le_log (by positivity)
  have h1 : 1 ≤ 1 / ε := by rw [le_div_iff₀ hε]; linarith
  have h2 : ℓ * m / ε = ℓ * m * (1 / ε) := by ring
  rw [h2]
  have h3 : 0 ≤ ℓ * m := mul_nonneg hℓ hm.le
  nlinarith

end UnforcedLeray.ComplexODE

namespace UnforcedLeray.Rayleigh.Evans

open UnforcedLeray.ComplexODE Sturm GaussianPotential

theorem neutralOmega_antitone : Antitone neutralOmega := by
  intro x y hxy
  unfold neutralOmega neutralRadius
  apply Real.exp_le_exp.mpr
  have := Real.exp_le_exp.mpr (by linarith : 2 * x ≤ 2 * y)
  linarith

/-- On `[a, b]` the Gaussian angular speed stays at distance `≥ m |t - τ|` from any real
level, for a suitable `τ ∈ [a, b]` depending on the level. -/
theorem exists_center_abs_neutralOmega_sub {a b : ℝ} (hab : a ≤ b) :
    ∃ m > 0, ∀ x : ℝ, ∃ τ ∈ Icc a b, ∀ t ∈ Icc a b, m * |t - τ| ≤ |neutralOmega t - x| := by
  set Ω' : ℝ → ℝ := fun x => -2 * neutralRadius x * neutralOmega x with hΩ'
  have hΩ'c : Continuous Ω' := by
    rw [hΩ']
    exact (continuous_const.mul continuous_neutralRadius).mul continuous_neutralOmega
  have hΩ'pos : ∀ x, 0 < |Ω' x| := by
    intro x
    apply abs_pos.mpr
    have h1 := neutralRadius_pos x
    have h2 : 0 < neutralOmega x := Real.exp_pos _
    rw [hΩ']
    exact (mul_neg_of_neg_of_pos (by linarith) h2).ne
  obtain ⟨x₀, -, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hab)
    (hΩ'c.abs.continuousOn (s := Icc a b))
  have hsep := mul_abs_sub_le_abs_sub_of_deriv (F := neutralOmega) (F' := Ω')
    (fun x => hasDerivAt_neutralOmega x) (fun x hx => hmin hx)
  refine ⟨|Ω' x₀|, hΩ'pos x₀, fun x => ?_⟩
  have haI : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hbI : b ∈ Icc a b := ⟨hab, le_rfl⟩
  by_cases hxa : neutralOmega a ≤ x
  · refine ⟨a, haI, fun t ht => ?_⟩
    have h := hsep a haI t ht
    have hmono : neutralOmega t ≤ neutralOmega a := neutralOmega_antitone ht.1
    rw [abs_of_nonpos (by linarith : neutralOmega t - neutralOmega a ≤ 0)] at h
    rw [abs_of_nonpos (by linarith : neutralOmega t - x ≤ 0)]
    linarith
  by_cases hxb : x ≤ neutralOmega b
  · refine ⟨b, hbI, fun t ht => ?_⟩
    have h := hsep b hbI t ht
    have hmono : neutralOmega b ≤ neutralOmega t := neutralOmega_antitone ht.2
    rw [abs_of_nonneg (by linarith : 0 ≤ neutralOmega t - neutralOmega b)] at h
    rw [abs_of_nonneg (by linarith : 0 ≤ neutralOmega t - x)]
    linarith
  push Not at hxa hxb
  obtain ⟨τ, hτ, hτx⟩ := intermediate_value_Icc' hab continuous_neutralOmega.continuousOn
    ⟨hxb.le, hxa.le⟩
  refine ⟨τ, hτ, fun t ht => ?_⟩
  have h := hsep τ hτ t ht
  rwa [hτx] at h

theorem norm_ofReal_sub_ge_half (r : ℝ) (c : ℂ) :
    (|r - c.re| + c.im) / 2 ≤ ‖(r : ℂ) - c‖ := by
  have h1 : |r - c.re| ≤ ‖(r : ℂ) - c‖ := by
    have h := Complex.abs_re_le_norm ((r : ℂ) - c)
    simpa using h
  have h2 : c.im ≤ ‖(r : ℂ) - c‖ := by
    have h := Complex.abs_im_le_norm ((r : ℂ) - c)
    simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, abs_neg] at h
    exact (le_abs_self _).trans h
  linarith

/-- **Logarithmic kernel bound.** On `[a, b]`, for `0 < Im c ≤ 1` and arbitrary `Re c`,
`∫_a^b W/|Ω - c| ≤ C (1 + log (1/Im c))`. -/
theorem exists_integral_Wlog_div_norm_le_log {a b : ℝ} (hab : a ≤ b) :
    ∃ C ≥ 0, ∀ c : ℂ, 0 < c.im → c.im ≤ 1 →
      (∫ t in a..b, Wlog t / ‖(neutralOmega t : ℂ) - c‖) ≤ C * (1 + Real.log (1 / c.im)) := by
  obtain ⟨m, hm, hcenter⟩ := exists_center_abs_neutralOmega_sub hab
  set Lg : ℝ := Real.log (1 + (b - a) * m) with hLg
  have hLg0 : 0 ≤ Lg := Real.log_nonneg (by nlinarith [sub_nonneg.mpr hab])
  refine ⟨32 / m * (Lg + 1), by positivity, fun c hc hc1 => ?_⟩
  set ε := c.im with hεdef
  obtain ⟨τ, hτ, hτb⟩ := hcenter c.re
  have hεm : 0 < ε / m := div_pos hc hm
  have hcont : Continuous (fun t => Wlog t / ‖(neutralOmega t : ℂ) - c‖) :=
    continuous_Wlog_div_norm hc
  have hpt : ∀ t ∈ Icc a b, Wlog t / ‖(neutralOmega t : ℂ) - c‖ ≤
      16 / m * (|t - τ| + ε / m)⁻¹ := by
    intro t ht
    have hW := Wlog_le_eight t
    have hW0 := (Wlog_pos t).le
    have hlow : (m * |t - τ| + ε) / 2 ≤ ‖(neutralOmega t : ℂ) - c‖ := by
      have h := norm_ofReal_sub_ge_half (neutralOmega t) c
      have h' := hτb t ht
      linarith
    have hpos : 0 < (m * |t - τ| + ε) / 2 := by positivity
    have hden : 0 < ‖(neutralOmega t : ℂ) - c‖ := hpos.trans_le hlow
    have heq : 16 / m * (|t - τ| + ε / m)⁻¹ = 8 / ((m * |t - τ| + ε) / 2) := by
      field_simp
      ring
    rw [heq]
    calc Wlog t / ‖(neutralOmega t : ℂ) - c‖ ≤ 8 / ‖(neutralOmega t : ℂ) - c‖ :=
          div_le_div_of_nonneg_right hW hden.le
      _ ≤ 8 / ((m * |t - τ| + ε) / 2) := div_le_div_of_nonneg_left (by norm_num) hpos hlow
  have hint : (∫ t in a..b, Wlog t / ‖(neutralOmega t : ℂ) - c‖) ≤
      16 / m * (Real.log ((τ - a + ε / m) / (ε / m)) + Real.log ((b - τ + ε / m) / (ε / m))) := by
    rw [← integral_inv_abs_add hτ.1 hτ.2 hεm, ← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_mono_on hab (hcont.intervalIntegrable a b)
      ((continuous_const.mul (continuous_inv_abs_add hεm τ)).intervalIntegrable a b) hpt
  have hl1 := log_ratio_le (sub_nonneg.mpr hτ.1) hm hc hc1
  have hl2 := log_ratio_le (sub_nonneg.mpr hτ.2) hm hc hc1
  have hm1 : Real.log (1 + (τ - a) * m) ≤ Lg :=
    Real.log_le_log (by nlinarith [sub_nonneg.mpr hτ.1]) (by nlinarith [hτ.2])
  have hm2 : Real.log (1 + (b - τ) * m) ≤ Lg :=
    Real.log_le_log (by nlinarith [sub_nonneg.mpr hτ.2]) (by nlinarith [hτ.1])
  have hlog0 : 0 ≤ Real.log (1 / ε) := Real.log_nonneg (by rw [le_div_iff₀ hc]; linarith)
  have hsum : Real.log ((τ - a + ε / m) / (ε / m)) + Real.log ((b - τ + ε / m) / (ε / m)) ≤
      2 * ((Lg + 1) * (1 + Real.log (1 / ε))) := by
    nlinarith
  calc (∫ t in a..b, Wlog t / ‖(neutralOmega t : ℂ) - c‖)
      ≤ 16 / m * (Real.log ((τ - a + ε / m) / (ε / m)) +
          Real.log ((b - τ + ε / m) / (ε / m))) := hint
    _ ≤ 16 / m * (2 * ((Lg + 1) * (1 + Real.log (1 / ε)))) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 32 / m * (Lg + 1) * (1 + Real.log (1 / ε)) := by ring

end UnforcedLeray.Rayleigh.Evans
