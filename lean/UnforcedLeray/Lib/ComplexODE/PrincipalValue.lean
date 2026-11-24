import UnforcedLeray.Lib.ComplexODE.CriticalCauchy

/-!
# The principal-value part of `I₊` is an absolutely convergent integral (INF18 O2 supplement)

Wave 1 block 1H part 3, scoping note

`Iplus a b g` contains the real integral of `W g/(Ω - a_*) - (W g)(t_*)/(Ω'(t_*)(t - t_*))`.
This module proves that this integrand is interval integrable, so that integral is a genuine
Lebesgue integral and not Lean's default value for a nonintegrable function. The integrand is
bounded on `[a, b] \ {t_*}` (`intervalIntegrable_cauchy_principal`); at `t = t_*` both real
quotients take Lean's value `0`, which does not affect the integral.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped Interval ContDiff

namespace UnforcedLeray.ComplexODE

/-- Under the hypotheses of `tendsto_integral_cauchy_remainder`, the principal-value integrand
`f/Φ - f(s)/(d (t - s))` is interval integrable on `[a, b]`. -/
theorem intervalIntegrable_cauchy_principal {a b s d m L K : ℝ} {Φ f : ℝ → ℝ}
    (hab : a ≤ b) (hd : d ≠ 0) (hm : 0 < m) (hL : 0 ≤ L) (hK : 0 ≤ K)
    (hΦc : Continuous Φ) (hfc : Continuous f)
    (h1 : ∀ t ∈ Icc a b, m * |t - s| ≤ |Φ t|)
    (h2 : ∀ t ∈ Icc a b, |f t - f s| ≤ L * |t - s|)
    (h3 : ∀ t ∈ Icc a b, |Φ t - d * (t - s)| ≤ K * (t - s) ^ 2) :
    IntervalIntegrable (fun t => f t / Φ t - f s / (d * (t - s))) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  have hdabs : 0 < |d| := abs_pos.mpr hd
  set C₁ : ℝ := L / m with hC₁
  set C₂ : ℝ := |f s| * K / (m * |d|) with hC₂
  have hC₁0 : 0 ≤ C₁ := div_nonneg hL hm.le
  have hC₂0 : 0 ≤ C₂ := div_nonneg (mul_nonneg (abs_nonneg _) hK) (by positivity)
  apply Measure.integrableOn_of_bounded (M := C₁ + C₂) measure_Ioc_lt_top.ne
  · exact ((hfc.measurable.div hΦc.measurable).sub (measurable_const.div
      (measurable_const.mul (measurable_id.sub measurable_const)))).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioc,
      ae_restrict_of_ae ((volume : Measure ℝ).ae_ne s)] with t ht hts
    have htI : t ∈ Icc a b := ⟨ht.1.le, ht.2⟩
    set A : ℝ := Φ t with hA
    set B : ℝ := d * (t - s) with hB
    have he : 0 < |t - s| := abs_pos.mpr (sub_ne_zero.mpr hts)
    have hAm : m * |t - s| ≤ |A| := h1 t htI
    have hApos : 0 < |A| := lt_of_lt_of_le (mul_pos hm he) hAm
    have hBabs : |B| = |d| * |t - s| := by rw [hB, abs_mul]
    have hBpos : 0 < |B| := by rw [hBabs]; positivity
    have hA0 : A ≠ 0 := abs_pos.mp hApos
    have hB0 : B ≠ 0 := abs_pos.mp hBpos
    have hid : f t / A - f s / B = (f t - f s) / A + f s * (B - A) / (A * B) := by
      field_simp
      ring
    rw [Real.norm_eq_abs, hid]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_div, div_le_iff₀ hApos]
      calc |f t - f s| ≤ L * |t - s| := h2 t htI
        _ = C₁ * (m * |t - s|) := by rw [hC₁]; field_simp
        _ ≤ C₁ * |A| := mul_le_mul_of_nonneg_left hAm hC₁0
    · rw [abs_div, abs_mul, abs_mul, div_le_iff₀ (mul_pos hApos hBpos)]
      have hBA : |B - A| ≤ K * |t - s| ^ 2 := by
        rw [abs_sub_comm, sq_abs]
        exact h3 t htI
      calc |f s| * |B - A| ≤ |f s| * (K * |t - s| ^ 2) :=
            mul_le_mul_of_nonneg_left hBA (abs_nonneg _)
        _ = C₂ * ((m * |t - s|) * (|d| * |t - s|)) := by rw [hC₂]; field_simp
        _ ≤ C₂ * (|A| * |B|) := by
          rw [hBabs]
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hAm (by positivity)) hC₂0

end UnforcedLeray.ComplexODE

namespace UnforcedLeray.Rayleigh.Evans

open UnforcedLeray.ComplexODE Sturm GaussianPotential

/-- On `[a, b]`, `|Ω y - Ω x| ≥ m |y - x|` for some `m > 0` (`|Ω'| ≥ m` and the mean value
theorem). -/
theorem exists_neutralOmega_separation {a b : ℝ} (hab : a ≤ b) :
    ∃ m > 0, ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, m * |y - x| ≤ |neutralOmega y - neutralOmega x| := by
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
  exact ⟨|Ω' x₀|, hΩ'pos x₀, mul_abs_sub_le_abs_sub_of_deriv (F := neutralOmega) (F' := Ω')
    (fun x => hasDerivAt_neutralOmega x) (fun x hx => hmin hx)⟩

/-- The real integrand in `Iplus a b g` is interval integrable for every `C¹` weight `g` when
`a < t_* < b`. -/
theorem intervalIntegrable_Iplus_integrand {a b : ℝ} (ha : a < neutralCriticalTime)
    (hb : neutralCriticalTime < b) {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) :
    IntervalIntegrable (fun t => Wlog t * g t / (neutralOmega t - gaussianCriticalSpeed) -
      Wlog neutralCriticalTime * g neutralCriticalTime /
        (deriv neutralOmega neutralCriticalTime * (t - neutralCriticalTime))) volume a b := by
  set s := neutralCriticalTime with hs
  set d := deriv neutralOmega s with hd
  have hd0 : d < 0 := deriv_neutralOmega_critical_neg
  have hsI : s ∈ Icc a b := ⟨ha.le, hb.le⟩
  obtain ⟨m, hm, hcenter⟩ := exists_neutralOmega_separation (ha.trans hb).le
  have h1 : ∀ t ∈ Icc a b, m * |t - s| ≤ |neutralOmega t - gaussianCriticalSpeed| := by
    intro t ht
    have h := hcenter s hsI t ht
    rwa [neutralOmega_critical_eq] at h
  have hf : ContDiff ℝ 1 (fun t => Wlog t * g t) :=
    (contDiff_infty.mp Wlog_smooth 1).mul hg
  obtain ⟨L, hL, hLip⟩ := exists_lipschitz_Icc hf a b
  obtain ⟨K, hK, hTay⟩ := exists_taylor_two_Icc neutralOmega_smooth a b
  exact intervalIntegrable_cauchy_principal (Φ := fun t => neutralOmega t - gaussianCriticalSpeed)
    (f := fun t => Wlog t * g t) (ha.trans hb).le hd0.ne hm hL hK
    (continuous_neutralOmega.sub continuous_const) hf.continuous h1
    (fun t ht => hLip s hsI t ht)
    (fun t ht => by
      have h := hTay s hsI t ht
      rwa [neutralOmega_critical_eq] at h)

end UnforcedLeray.Rayleigh.Evans
