import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

/-!
# B0425: the periodic center-averaging identity (`eq:free-stress-16`)

Blueprint unit B0425, label `eq:free-stress-16`, `paper/main.tex` lines 7519--7524.

For every nonnegative `P`-periodic density `h` on `ℝ` and every bounded interval `I`,
the manuscript asserts `∫₀^P ∫_I h(τ₀ + t) dt dτ₀ = |I| ∫₀^P h(τ) dτ` (lines 7519--7524).
It is used on line 7526 to integrate the window estimate `eq:free-stress-15` in its center
`τ₀`. The proof is Tonelli followed by translation invariance of the integral of a periodic
function over one period.

We formalize the identity in two forms.

* `lintegral_center_average`: the faithful form for an `ℝ≥0∞`-valued measurable `P`-periodic
  density, with lower Lebesgue integrals. No integrability is needed, and the identity holds for
  every set `I ⊆ ℝ` (with `|I| = volume I`), in particular for every bounded interval; it also
  holds for every real `P` (for `P ≤ 0` both sides vanish since `Ioc 0 P = ∅`).
  `lintegral_center_average_Icc` specializes to `I = [a, b]`, `|I| = b - a`.
* `integral_center_average`: the real-valued form with Bochner interval integrals, for a
  measurable nonnegative real `P`-periodic `h` that is integrable over one period
  (`0 ≤ P`). The integrability hypothesis is the one the manuscript has implicitly (there
  `h = ‖f(τ)‖^q` or `‖w(τ)‖^q` with `f, w ∈ Y_q`); without it the real identity is false in
  Lean, because the Bochner integral of a non-integrable function is `0`.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal

namespace UnforcedLeray.B0425

/-- Translation invariance of the integral over a period: for a `P`-periodic density `h`,
`∫₀^P h(τ₀ + t) dτ₀ = ∫₀^P h(τ) dτ` for every shift `t`. -/
theorem lintegral_Ioc_shift_eq {h : ℝ → ℝ≥0∞} {P : ℝ} (hper : Function.Periodic h P) (t : ℝ) :
    ∫⁻ τ₀ in Ioc 0 P, h (τ₀ + t) = ∫⁻ τ in Ioc 0 P, h τ := by
  rcases le_or_gt P 0 with hP | hP
  · simp [Set.Ioc_eq_empty (not_lt.2 hP)]
  have h1 : ∫⁻ τ₀ in Ioc 0 P, h (τ₀ + t) = ∫⁻ τ in Ioc t (t + P), h τ := by
    have := (measurePreserving_add_right (volume : Measure ℝ) t).setLIntegral_comp_preimage_emb
      (measurableEmbedding_addRight t) h (Ioc t (t + P))
    rw [Set.preimage_add_const_Ioc] at this
    simpa using this
  rw [h1]
  have : VAddInvariantMeasure (AddSubgroup.zmultiples P) ℝ volume :=
    ⟨fun c s _ => measure_preimage_add _ _ _⟩
  have h2 := IsAddFundamentalDomain.setLIntegral_eq (G := AddSubgroup.zmultiples P)
    (isAddFundamentalDomain_Ioc hP t) (isAddFundamentalDomain_Ioc hP 0) h
    hper.map_vadd_zmultiples
  simpa using h2

/-- **Periodic center-averaging identity** (`eq:free-stress-16`, `paper/main.tex`
lines 7519--7524): for a nonnegative (here `ℝ≥0∞`-valued) measurable `P`-periodic density `h`
and any set `I ⊆ ℝ` (in particular any bounded interval),
`∫₀^P ∫_I h(τ₀ + t) dt dτ₀ = |I| ∫₀^P h(τ) dτ`. -/
theorem lintegral_center_average {h : ℝ → ℝ≥0∞} {P : ℝ} (hmeas : Measurable h)
    (hper : Function.Periodic h P) (I : Set ℝ) :
    ∫⁻ τ₀ in Ioc 0 P, ∫⁻ t in I, h (τ₀ + t) = volume I * ∫⁻ τ in Ioc 0 P, h τ := by
  have hm : Measurable (Function.uncurry fun τ₀ t : ℝ => h (τ₀ + t)) :=
    hmeas.comp (measurable_fst.add measurable_snd)
  rw [lintegral_lintegral_swap hm.aemeasurable]
  simp_rw [lintegral_Ioc_shift_eq hper]
  rw [setLIntegral_const, mul_comm]

/-- `eq:free-stress-16` (`paper/main.tex` lines 7519--7524) for the bounded interval
`I = [a, b]`, `|I| = b - a`: the form in which it is applied to the windows `[-1, 1]` and
`[-2, 2]` of `eq:free-stress-15`. -/
theorem lintegral_center_average_Icc {h : ℝ → ℝ≥0∞} {P : ℝ} (hmeas : Measurable h)
    (hper : Function.Periodic h P) (a b : ℝ) :
    ∫⁻ τ₀ in Ioc 0 P, ∫⁻ t in Icc a b, h (τ₀ + t) =
      ENNReal.ofReal (b - a) * ∫⁻ τ in Ioc 0 P, h τ := by
  rw [lintegral_center_average hmeas hper, Real.volume_Icc]

/-- Real-valued form of `eq:free-stress-16` for `a ≤ b`. -/
theorem integral_center_average_of_le {h : ℝ → ℝ} {P : ℝ} (hP : 0 ≤ P) (hmeas : Measurable h)
    (hnn : ∀ τ, 0 ≤ h τ) (hper : Function.Periodic h P)
    (hint : IntervalIntegrable h volume 0 P) {a b : ℝ} (hab : a ≤ b) :
    ∫ τ₀ in (0)..P, ∫ t in a..b, h (τ₀ + t) = (b - a) * ∫ τ in (0)..P, h τ := by
  set H : ℝ → ℝ≥0∞ := fun τ => ENNReal.ofReal (h τ) with hH
  have hHm : Measurable H := ENNReal.measurable_ofReal.comp hmeas
  have hHper : Function.Periodic H P := fun τ => by simp only [hH, hper τ]
  set F : ℝ → ℝ≥0∞ := fun τ₀ => ∫⁻ t in Ioc a b, H (τ₀ + t) with hF
  have hFm : Measurable F := by
    have hm : Measurable (Function.uncurry fun τ₀ t : ℝ => H (τ₀ + t)) :=
      hHm.comp (measurable_fst.add measurable_snd)
    exact hm.lintegral_prod_right
  -- the inner integral is the real part of `F`
  have hinner : ∀ τ₀ : ℝ, ∫ t in a..b, h (τ₀ + t) = (F τ₀).toReal := by
    intro τ₀
    rw [intervalIntegral.integral_of_le hab]
    exact integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun t => hnn _)
      ((hmeas.comp (measurable_const_add τ₀)).aestronglyMeasurable)
  -- finiteness of the period integral of `H`
  have hIoc : IntegrableOn h (Ioc 0 P) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hP).1 hint
  have hHfin : ∫⁻ τ in Ioc 0 P, H τ < ∞ := hIoc.lintegral_lt_top
  have hFint : ∫⁻ τ₀ in Ioc 0 P, F τ₀ = ENNReal.ofReal (b - a) * ∫⁻ τ in Ioc 0 P, H τ := by
    rw [hF, lintegral_center_average hHm hHper, Real.volume_Ioc]
  have hFfin : ∫⁻ τ₀ in Ioc 0 P, F τ₀ ≠ ∞ := by
    rw [hFint]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hHfin.ne
  simp_rw [hinner]
  rw [intervalIntegral.integral_of_le hP, intervalIntegral.integral_of_le hP,
    integral_toReal hFm.aemeasurable (ae_lt_top' hFm.aemeasurable hFfin), hFint,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (sub_nonneg.2 hab),
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hnn)
      hmeas.aestronglyMeasurable]

/-- **Periodic center-averaging identity, real-valued form** (`eq:free-stress-16`,
`paper/main.tex` lines 7519--7524): for a measurable nonnegative real `P`-periodic `h`
integrable over one period, and every bounded interval with endpoints `a, b`,
`∫₀^P ∫_a^b h(τ₀ + t) dt dτ₀ = (b - a) ∫₀^P h(τ) dτ`. (For `b < a` both sides change sign.) -/
theorem integral_center_average {h : ℝ → ℝ} {P : ℝ} (hP : 0 ≤ P) (hmeas : Measurable h)
    (hnn : ∀ τ, 0 ≤ h τ) (hper : Function.Periodic h P)
    (hint : IntervalIntegrable h volume 0 P) (a b : ℝ) :
    ∫ τ₀ in (0)..P, ∫ t in a..b, h (τ₀ + t) = (b - a) * ∫ τ in (0)..P, h τ := by
  rcases le_total a b with hab | hba
  · exact integral_center_average_of_le hP hmeas hnn hper hint hab
  · have := integral_center_average_of_le hP hmeas hnn hper hint hba
    simp_rw [intervalIntegral.integral_symm b a]
    rw [intervalIntegral.integral_neg, this]
    ring

end UnforcedLeray.B0425
