import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_5_2_1_2

/-!
# `PartIII-b:C/rep/5/2/1/2`: chart Jacobian `ChartJacobian`

Source `the November 2 reference manuscript` 2683-2689, step (iii):
under `r = R/√s`, `z = η/√s`, `π s^{-5/2} ds dη = R^{-2}·2πr dr dz`.
Proof: the inner `η`-integral is a linear change of variables `η = √s z` (lemma
`lintegral_div_scale`); the outer `s`-integral is the change of variables `s = R²/r²` on `(0,∞)`
(one-dimensional Jacobian lemma), and the pointwise identity
`(2R²/r³)·π(r⁴/R⁴) = R⁻²·2πr`.
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Linear change of variables on the whole line: `∫ G = k ∫ G(k·)` for `k > 0`. -/
lemma lintegral_univ_scale {k : ℝ} (hk : 0 < k) (G : ℝ → ℝ≥0∞) :
    ∫⁻ x, G x = ENNReal.ofReal k * ∫⁻ x, G (k * x) := by
  have himg : (fun x => k * x) '' (univ : Set ℝ) = univ := by
    ext y
    simp only [mem_image, mem_univ, true_and, iff_true]
    exact ⟨y / k, by field_simp⟩
  have hd : ∀ x ∈ (univ : Set ℝ), HasDerivWithinAt (fun x => k * x) k univ x := by
    intro x _
    have h : HasDerivAt (fun x => k * x) (k * 1) x := (hasDerivAt_id' x).const_mul k
    rw [mul_one] at h
    exact h.hasDerivWithinAt
  have hinj : InjOn (fun x => k * x) univ := fun x _ y _ h => mul_left_cancel₀ hk.ne' h
  have h := MeasureTheory.lintegral_image_eq_lintegral_abs_deriv_mul MeasurableSet.univ hd hinj G
  simp only [himg, Measure.restrict_univ, abs_of_pos hk] at h
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at h
  exact h

/-- `∫ G(x/k) dx = k ∫ G` for `k > 0`. -/
lemma lintegral_div_scale {k : ℝ} (hk : 0 < k) (G : ℝ → ℝ≥0∞) :
    ∫⁻ x, G (x / k) = ENNReal.ofReal k * ∫⁻ x, G x := by
  have h := lintegral_univ_scale hk (fun x => G (x / k))
  have e : ∀ x : ℝ, k * x / k = x := fun x => mul_div_cancel_left₀ x hk.ne'
  simp only [e] at h
  exact h

/-- Chart Jacobian (step (iii)), the statement `ChartJacobian`. -/
theorem chartJacobian : ChartJacobian := by
  intro R hR Ψ _hΨ
  have hR0 : R ≠ 0 := hR.ne'
  -- inner `η`-integral and the exponent identity
  have step1 : ∀ s ∈ Ioi (0 : ℝ),
      ∫⁻ η : ℝ, ENNReal.ofReal (Real.pi * s ^ (-5 / 2 : ℝ)) * Ψ (R / Real.sqrt s) (η / Real.sqrt s)
        = ENNReal.ofReal (Real.pi * s ^ (-2 : ℝ)) * ∫⁻ z : ℝ, Ψ (R / Real.sqrt s) z := by
    intro s hs
    have hs' : 0 < s := Set.mem_Ioi.1 hs
    have hsq : 0 < Real.sqrt s := Real.sqrt_pos.2 hs'
    have hp : 0 ≤ Real.pi * s ^ (-5 / 2 : ℝ) :=
      mul_nonneg Real.pi_pos.le (Real.rpow_nonneg hs'.le _)
    have hid : Real.pi * s ^ (-5 / 2 : ℝ) * Real.sqrt s = Real.pi * s ^ (-2 : ℝ) := by
      rw [Real.sqrt_eq_rpow, mul_assoc, ← Real.rpow_add hs']
      norm_num
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_div_scale hsq (Ψ (R / Real.sqrt s)), ← mul_assoc, ← ENNReal.ofReal_mul hp, hid]
  -- outer `s`-integral: the derivative and injectivity of `r ↦ R²/r²` on `(0, ∞)`
  have hder : ∀ r : ℝ, 0 < r →
      HasDerivWithinAt (fun r : ℝ => R ^ 2 / r ^ 2) (-(2 * R ^ 2 / r ^ 3)) (Ioi 0) r := by
    intro r hr
    have hr0 : r ≠ 0 := hr.ne'
    have h1 : HasDerivAt (fun x : ℝ => x ^ 2) (2 * r) r := by
      simpa using hasDerivAt_pow 2 r
    have h2 := (h1.inv (pow_ne_zero 2 hr0)).const_mul (R ^ 2)
    have h3 : HasDerivAt (fun x : ℝ => R ^ 2 / x ^ 2) (-(2 * R ^ 2 / r ^ 3)) r := by
      have hfun : (fun x : ℝ => R ^ 2 / x ^ 2) = (fun x : ℝ => R ^ 2 * (x ^ 2)⁻¹) := by
        funext x
        rw [div_eq_mul_inv]
      have hd : -(2 * R ^ 2 / r ^ 3) = R ^ 2 * (-(2 * r) / (r ^ 2) ^ 2) := by
        field_simp
      rw [hfun, hd]
      exact h2
    exact h3.hasDerivWithinAt
  have hinj : InjOn (fun r : ℝ => R ^ 2 / r ^ 2) (Ioi 0) := by
    intro x hx y hy hxy
    have hx' : 0 < x := Set.mem_Ioi.1 hx
    have hy' : 0 < y := Set.mem_Ioi.1 hy
    have hxy' := hxy
    simp only at hxy'
    rw [div_eq_div_iff (pow_ne_zero 2 hx'.ne') (pow_ne_zero 2 hy'.ne')] at hxy'
    have h2 : y ^ 2 = x ^ 2 := mul_left_cancel₀ (pow_ne_zero 2 hR0) hxy'
    exact ((pow_left_inj₀ hx'.le hy'.le two_ne_zero).1 h2.symm)
  have himg : (fun r : ℝ => R ^ 2 / r ^ 2) '' Ioi 0 = Ioi 0 := by
    ext s
    constructor
    · rintro ⟨r, hr, rfl⟩
      have hr' : 0 < r := Set.mem_Ioi.1 hr
      exact Set.mem_Ioi.2 (div_pos (pow_pos hR 2) (pow_pos hr' 2))
    · intro hs
      have hs' : 0 < s := Set.mem_Ioi.1 hs
      refine ⟨R / Real.sqrt s, Set.mem_Ioi.2 (div_pos hR (Real.sqrt_pos.2 hs')), ?_⟩
      show R ^ 2 / (R / Real.sqrt s) ^ 2 = s
      rw [div_pow, Real.sq_sqrt hs'.le]
      field_simp
  have hcov := MeasureTheory.lintegral_image_eq_lintegral_abs_deriv_mul (s := Ioi (0 : ℝ))
    (f := fun r : ℝ => R ^ 2 / r ^ 2) (f' := fun r : ℝ => -(2 * R ^ 2 / r ^ 3))
    (g := fun s : ℝ => ENNReal.ofReal (Real.pi * s ^ (-2 : ℝ)) * ∫⁻ z : ℝ, Ψ (R / Real.sqrt s) z)
    measurableSet_Ioi (fun r hr => hder r (Set.mem_Ioi.1 hr)) hinj
  rw [himg] at hcov
  rw [setLIntegral_congr_fun measurableSet_Ioi step1]
  rw [hcov]
  have hpt : ∀ r ∈ Ioi (0 : ℝ),
      ENNReal.ofReal |-(2 * R ^ 2 / r ^ 3)| *
        (ENNReal.ofReal (Real.pi * (R ^ 2 / r ^ 2) ^ (-2 : ℝ)) *
          ∫⁻ z : ℝ, Ψ (R / Real.sqrt (R ^ 2 / r ^ 2)) z)
      = ENNReal.ofReal (R⁻¹ ^ 2) * ∫⁻ z : ℝ, ENNReal.ofReal (2 * Real.pi * r) * Ψ r z := by
    intro r hr
    have hr' : 0 < r := Set.mem_Ioi.1 hr
    have hr0 : r ≠ 0 := hr'.ne'
    have hsq : Real.sqrt (R ^ 2 / r ^ 2) = R / r := by
      rw [← div_pow, Real.sqrt_sq (div_pos hR hr').le]
    have hRdiv : R / (R / r) = r := by field_simp
    rw [hsq, hRdiv, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    have hpow : (R ^ 2 / r ^ 2) ^ (-2 : ℝ) = r ^ 4 / R ^ 4 := by
      rw [Real.rpow_neg (by positivity), Real.rpow_two]
      field_simp
    have hpos : 0 < 2 * R ^ 2 / r ^ 3 := div_pos (mul_pos two_pos (pow_pos hR 2)) (pow_pos hr' 3)
    have h1nn : 0 ≤ 2 * R ^ 2 / r ^ 3 := hpos.le
    have h3nn : (0 : ℝ) ≤ R⁻¹ ^ 2 := by positivity
    have key : 2 * R ^ 2 / r ^ 3 * (Real.pi * (r ^ 4 / R ^ 4)) = R⁻¹ ^ 2 * (2 * Real.pi * r) := by
      field_simp
    rw [hpow, abs_neg, abs_of_pos hpos]
    rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul h1nn, ← ENNReal.ofReal_mul h3nn, key]
  rw [setLIntegral_congr_fun measurableSet_Ioi hpt, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

end UnforcedLeray.Short.PartIIIb.Concrete
