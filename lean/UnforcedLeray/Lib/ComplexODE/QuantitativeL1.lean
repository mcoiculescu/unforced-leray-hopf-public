import UnforcedLeray.Lib.ComplexODE.L1Dependence

/-!
# Quantitative L¹ dependence on the speed (INF18 target O3)

Wave 1 block 1H part 3, scoping note

bypass B8 (ii): "the L¹ dependence gives sup |F - N| ≤ C (|α² - β²| + |z| ⋯)". Blueprint unit
B0034 (Lin's continuation, `paper/main.tex` lines 1011--1021).

The Rayleigh coefficient `V_β(c) = β² + k/(Ω - c)` and the completed neutral coefficient
`α² - W` differ by the exact Gaussian cancellation (`rayleighPotential_sub_neutral`)
`(β² - α²) - W (c - a_*)/(Ω - c)`, `a_* = e^{-2}`. Hence the L¹ distance of the coefficients on
`[a, b]` is at most
`P = |β² - α²| (b - a) + |c - a_*| ∫_a^b W/|Ω - c|` (`neutralPerturbationSize`), and the
integral Gronwall estimate of the copied draft (`norm_sub_le_integral_of_isSolOn`) gives
`|(F_β(c) - N_α, F_β(c)' - N_α')| ≤ C P e^P` on `[a, b]`, with `C` depending on `α, a, b` only.

**Deviation from the scoping signature.** The proposed O3 statement has no smallness
hypothesis and no factor `e^P`. Without either it is false: for fixed `c` and `β → ∞` the
left side grows like `e^{β(b-a)}/β`, the right side like `β²`. The version here carries the
factor `e^P` (`norm_normalizedPair_sub_neutral_le`) and gives the linear bound for `P ≤ 1`
(`norm_normalizedF_sub_neutral_le`), which is the regime used by the bifurcation O4.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Interval

namespace UnforcedLeray.Rayleigh.Evans

open NonUniqueEuler.LinODE Sturm GaussianPotential

/-- The exact Gaussian cancellation between the Rayleigh coefficient at `(β, c)` and the
completed neutral coefficient at `α` (statement of the draft

same name). -/
theorem rayleighPotential_sub_neutral (α β t : ℝ) {c : ℂ} (hc : 0 < c.im) :
    rayleighPotential β t c - neutralPotential α t =
      ((β : ℂ) ^ 2 - (α : ℂ) ^ 2) - (Wlog t : ℂ) *
        (c - (gaussianCriticalSpeed : ℂ)) / ((neutralOmega t : ℂ) - c) := by
  have hd := rayleigh_denominator_ne_zero hc t
  unfold rayleighPotential neutralPotential gaussianRayleighCoefficient gaussianOffset
  simp only [Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_sub]
  field_simp
  ring

/-- The L¹ size of the coefficient perturbation from `(α, a_*)` to `(β, c)` on `[a, b]`. -/
def neutralPerturbationSize (α β a b : ℝ) (c : ℂ) : ℝ :=
  |β ^ 2 - α ^ 2| * (b - a) +
    ‖c - (gaussianCriticalSpeed : ℂ)‖ * ∫ s in a..b, Wlog s / ‖(neutralOmega s : ℂ) - c‖

theorem continuous_Wlog_div_norm {c : ℂ} (hc : 0 < c.im) :
    Continuous (fun s => Wlog s / ‖(neutralOmega s : ℂ) - c‖) := by
  apply continuous_Wlog.div
  · exact ((Complex.continuous_ofReal.comp continuous_neutralOmega).sub continuous_const).norm
  · intro s
    exact norm_ne_zero_iff.mpr (rayleigh_denominator_ne_zero hc s)

theorem neutralPerturbationSize_nonneg (α β : ℝ) {a b : ℝ} (hab : a ≤ b) (c : ℂ) :
    0 ≤ neutralPerturbationSize α β a b c := by
  unfold neutralPerturbationSize
  have h1 : 0 ≤ ∫ s in a..b, Wlog s / ‖(neutralOmega s : ℂ) - c‖ :=
    intervalIntegral.integral_nonneg hab fun s _ => div_nonneg (Wlog_pos s).le (norm_nonneg _)
  have h2 : 0 ≤ b - a := sub_nonneg.mpr hab
  positivity

/-- The pointwise coefficient perturbation bound. -/
theorem norm_rayleighPotential_sub_neutral_le (α β t : ℝ) {c : ℂ} (hc : 0 < c.im) :
    ‖rayleighPotential β t c - neutralPotential α t‖ ≤
      |β ^ 2 - α ^ 2| + ‖c - (gaussianCriticalSpeed : ℂ)‖ *
        (Wlog t / ‖(neutralOmega t : ℂ) - c‖) := by
  rw [rayleighPotential_sub_neutral α β t hc]
  refine (norm_sub_le _ _).trans (le_of_eq ?_)
  congr 1
  · rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs]
  · rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Wlog_pos t)]
    ring

/-- The L¹ distance of the coefficients is at most `neutralPerturbationSize`. -/
theorem integral_norm_rayleighPotential_sub_neutral_le (α β : ℝ) {a b : ℝ} (hab : a ≤ b)
    {c : ℂ} (hc : 0 < c.im) :
    (∫ t in a..b, ‖rayleighPotential β t c - neutralPotential α t‖) ≤
      neutralPerturbationSize α β a b c := by
  have hcont : Continuous (fun t => rayleighPotential β t c - neutralPotential α t) :=
    (continuous_rayleighPotential β hc).sub (continuous_neutralPotential α)
  have hW := continuous_Wlog_div_norm hc
  calc (∫ t in a..b, ‖rayleighPotential β t c - neutralPotential α t‖)
      ≤ ∫ t in a..b, (|β ^ 2 - α ^ 2| + ‖c - (gaussianCriticalSpeed : ℂ)‖ *
          (Wlog t / ‖(neutralOmega t : ℂ) - c‖)) :=
        intervalIntegral.integral_mono_on hab (hcont.norm.intervalIntegrable a b)
          ((continuous_const.add (continuous_const.mul hW)).intervalIntegrable a b)
          (fun t _ => norm_rayleighPotential_sub_neutral_le α β t hc)
    _ = neutralPerturbationSize α β a b c := by
        rw [intervalIntegral.integral_add (f := fun _ => |β ^ 2 - α ^ 2|)
          (g := fun t => ‖c - (gaussianCriticalSpeed : ℂ)‖ *
            (Wlog t / ‖(neutralOmega t : ℂ) - c‖)) intervalIntegrable_const
          ((continuous_const.mul hW).intervalIntegrable a b),
          intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
          smul_eq_mul, neutralPerturbationSize]
        ring

/-- **INF18 O3, exponential form.** On a fixed interval `[a, b]` and for a fixed neutral
wavenumber `α` there is `C ≥ 0` such that for every `β` and every `c` with `Im c > 0`, the
normalized Rayleigh pair started at `a` differs from the normalized neutral pair, uniformly on
`[a, b]`, by at most `C P e^P`, `P = neutralPerturbationSize α β a b c`. -/
theorem norm_normalizedPair_sub_neutral_le (α : ℝ) {a b : ℝ} (hab : a ≤ b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (β : ℝ) (c : ℂ), 0 < c.im → ∀ t ∈ Icc a b,
      ‖(normalizedF β a c t - neutralNormalizedF α a t,
          normalizedDerivative β a c t - neutralNormalizedDerivative α a t)‖ ≤
        C * neutralPerturbationSize α β a b c *
          Real.exp (neutralPerturbationSize α β a b c) := by
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (neutralNormalizedF_smooth α a).continuous.continuousOn (s := Icc a b)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB a ⟨le_rfl, hab⟩)
  set M₀ : ℝ := ∫ t in a..b, ‖neutralPotential α t‖ with hM₀
  refine ⟨B * Real.exp ((b - a) + M₀), mul_nonneg hB0 (Real.exp_pos _).le, ?_⟩
  intro β c hc t ht
  have hV₁ : Continuous (fun s => rayleighPotential β s c) := continuous_rayleighPotential β hc
  have hV₀ : Continuous (neutralPotential α) := continuous_neutralPotential α
  have hest := norm_sub_le_integral_of_isSolOn hab hV₁.continuousOn hV₀.continuousOn
    ((normalizedPair_spec β a hc).1.mono (subset_univ _))
    ((neutralNormalizedPair_spec α a).1.mono (subset_univ _))
    (by rw [normalizedF_initial β a hc, neutralNormalizedF_initial])
    (by rw [normalizedDerivative_initial β a hc, neutralNormalizedDerivative_initial])
    hB t ht
  set P := neutralPerturbationSize α β a b c with hP
  have hD : (∫ s in a..b, ‖rayleighPotential β s c - neutralPotential α s‖) ≤ P :=
    integral_norm_rayleighPotential_sub_neutral_le α β hab hc
  have hD0 : 0 ≤ ∫ s in a..b, ‖rayleighPotential β s c - neutralPotential α s‖ :=
    intervalIntegral.integral_nonneg hab fun _ _ => norm_nonneg _
  have hmass : (∫ s in a..b, ‖rayleighPotential β s c‖) ≤ M₀ + P := by
    calc (∫ s in a..b, ‖rayleighPotential β s c‖)
        ≤ ∫ s in a..b, (‖rayleighPotential β s c - neutralPotential α s‖ +
            ‖neutralPotential α s‖) :=
          intervalIntegral.integral_mono_on hab (hV₁.norm.intervalIntegrable a b)
            (((hV₁.sub hV₀).norm.add hV₀.norm).intervalIntegrable a b)
            (fun s _ => norm_le_norm_sub_add _ _)
      _ = (∫ s in a..b, ‖rayleighPotential β s c - neutralPotential α s‖) + M₀ :=
          intervalIntegral.integral_add ((hV₁.sub hV₀).norm.intervalIntegrable a b)
            (hV₀.norm.intervalIntegrable a b)
      _ ≤ M₀ + P := by linarith
  have hexp : Real.exp ((b - a) + ∫ s in a..b, ‖rayleighPotential β s c‖) ≤
      Real.exp ((b - a) + M₀) * Real.exp P := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  calc _ ≤ (B * ∫ s in a..b, ‖rayleighPotential β s c - neutralPotential α s‖) *
        Real.exp ((b - a) + ∫ s in a..b, ‖rayleighPotential β s c‖) := hest
    _ ≤ (B * P) * (Real.exp ((b - a) + M₀) * Real.exp P) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hD hB0) hexp (Real.exp_pos _).le
          (mul_nonneg hB0 (hD0.trans hD))
    _ = B * Real.exp ((b - a) + M₀) * P * Real.exp P := by ring

/-- **INF18 O3, linear form.** On `[a, b]`, for fixed `α`, there is `C ≥ 0` such that for every
`β` and every `c` with `Im c > 0` and `P = neutralPerturbationSize α β a b c ≤ 1`,
`‖F_β(c) - N_α‖ ≤ C (|β² - α²| (b - a) + |c - a_*| ∫_a^b W/|Ω - c|)` on `[a, b]`, and the same
for the derivatives. -/
theorem norm_normalizedF_sub_neutral_le (α : ℝ) {a b : ℝ} (hab : a ≤ b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (β : ℝ) (c : ℂ), 0 < c.im → neutralPerturbationSize α β a b c ≤ 1 →
      ∀ t ∈ Icc a b,
        ‖normalizedF β a c t - neutralNormalizedF α a t‖ ≤
          C * neutralPerturbationSize α β a b c ∧
        ‖normalizedDerivative β a c t - neutralNormalizedDerivative α a t‖ ≤
          C * neutralPerturbationSize α β a b c := by
  obtain ⟨C, hC, hbound⟩ := norm_normalizedPair_sub_neutral_le α hab
  refine ⟨C * Real.exp 1, mul_nonneg hC (Real.exp_pos _).le, ?_⟩
  intro β c hc hP t ht
  have hP0 := neutralPerturbationSize_nonneg α β hab c
  have h := hbound β c hc t ht
  have hle : C * neutralPerturbationSize α β a b c *
      Real.exp (neutralPerturbationSize α β a b c) ≤
      C * Real.exp 1 * neutralPerturbationSize α β a b c := by
    have he := Real.exp_le_exp.mpr hP
    have hCP : 0 ≤ C * neutralPerturbationSize α β a b c := mul_nonneg hC hP0
    calc C * neutralPerturbationSize α β a b c * Real.exp (neutralPerturbationSize α β a b c)
        ≤ C * neutralPerturbationSize α β a b c * Real.exp 1 :=
          mul_le_mul_of_nonneg_left he hCP
      _ = C * Real.exp 1 * neutralPerturbationSize α β a b c := by ring
  exact ⟨(norm_fst_le _).trans (h.trans hle), (norm_snd_le _).trans (h.trans hle)⟩

end UnforcedLeray.Rayleigh.Evans
