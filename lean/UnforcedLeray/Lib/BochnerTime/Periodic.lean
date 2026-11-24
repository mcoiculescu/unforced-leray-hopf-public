import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Periodic phase: the center-averaging identity (INF14 target T9)


target T9; decision D2 of `scoping/README.md` §3 ("INF14 T9 supplies only the averaging identity
and mixed norms"). Manuscript `paper/main.tex` lines 7519–7524, equation `(free-stress-16)`
(blueprint unit B0425): for every nonnegative `P`-periodic density `h` and bounded interval `I`,

`∫_0^P ∫_I h(τ₀ + t) dt dτ₀ = |I| ∫_0^P h(τ) dτ`.

It is used to integrate the local estimate `(free-stress-15)` in its center and obtain the
global bound `(free-stress-17)`.

## Main results

* `lintegral_Ioc_comp_add_right`: the integral of a periodic function over a period is
  translation invariant;
* `lintegral_center_average`: `(free-stress-16)` for `ℝ≥0∞`-valued `h` (no integrability
  hypothesis; `I` may be any measurable set, and `|I| = volume I`);
* `integral_center_average`: the real-valued version for a nonnegative `h` integrable on a
  period and `I` of finite measure.

The other parts of T9 are in `BochnerTime.Translation` (translation continuity in
`L^p(AddCircle)`, from Mathlib's `Lp.instContinuousSMulDomMulAct`) and `BochnerTime.MixedNorm`
(the mixed norms `L^p_τ L^∞_y` of B0778).
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace UnforcedLeray.BochnerTime

/-- **Translation invariance over a period.** For a `P`-periodic `h : ℝ → ℝ≥0∞` and any `t`,
`∫_{(0,P]} h(τ + t) dτ = ∫_{(0,P]} h(τ) dτ`. -/
theorem lintegral_Ioc_comp_add_right {P : ℝ} (hP : 0 < P) {h : ℝ → ℝ≥0∞}
    (hper : Function.Periodic h P) (t : ℝ) :
    ∫⁻ τ in Ioc 0 P, h (τ + t) = ∫⁻ τ in Ioc 0 P, h τ := by
  have h1 : ∫⁻ τ in Ioc 0 P, h (τ + t) = ∫⁻ σ in Ioc t (t + P), h σ := by
    rw [← lintegral_indicator measurableSet_Ioc, ← lintegral_indicator measurableSet_Ioc]
    have hpt : ∀ τ, (Ioc 0 P).indicator (fun τ => h (τ + t)) τ =
        (Ioc t (t + P)).indicator h (τ + t) := by
      intro τ
      have hmem : τ ∈ Ioc 0 P ↔ τ + t ∈ Ioc t (t + P) := by
        simp only [mem_Ioc]
        constructor
        · rintro ⟨h1, h2⟩; constructor <;> linarith
        · rintro ⟨h1, h2⟩; constructor <;> linarith
      by_cases hτ : τ ∈ Ioc 0 P
      · rw [indicator_of_mem hτ, indicator_of_mem (hmem.1 hτ)]
      · rw [indicator_of_notMem hτ, indicator_of_notMem (fun h' => hτ (hmem.2 h'))]
    simp_rw [hpt]
    exact lintegral_add_right_eq_self (μ := volume) (fun σ => (Ioc t (t + P)).indicator h σ) t
  have : VAddInvariantMeasure (AddSubgroup.zmultiples P) ℝ volume :=
    ⟨fun c s _ => measure_preimage_add _ _ _⟩
  have h2 : ∫⁻ σ in Ioc t (t + P), h σ = ∫⁻ σ in Ioc 0 (0 + P), h σ :=
    (isAddFundamentalDomain_Ioc hP t).setLIntegral_eq (isAddFundamentalDomain_Ioc hP 0) h
      hper.map_vadd_zmultiples
  rw [h1, h2, zero_add]

/-- **Center-averaging identity** (T9; manuscript eq. `(free-stress-16)`, tex 7519–7524,
blueprint B0425). For a measurable `P`-periodic `h : ℝ → ℝ≥0∞` and a measurable set `I`,
`∫_{(0,P]} ∫_I h(τ₀ + t) dt dτ₀ = |I| ∫_{(0,P]} h(τ) dτ`. -/
theorem lintegral_center_average {P : ℝ} (hP : 0 < P) {h : ℝ → ℝ≥0∞} (hm : Measurable h)
    (hper : Function.Periodic h P) {I : Set ℝ} :
    ∫⁻ τ₀ in Ioc 0 P, ∫⁻ t in I, h (τ₀ + t) = volume I * ∫⁻ τ in Ioc 0 P, h τ := by
  have hmeas : AEMeasurable (Function.uncurry fun τ₀ t => h (τ₀ + t))
      ((volume.restrict (Ioc 0 P)).prod (volume.restrict I)) :=
    (hm.comp (measurable_fst.add measurable_snd)).aemeasurable
  rw [lintegral_lintegral_swap hmeas]
  simp_rw [lintegral_Ioc_comp_add_right hP hper]
  rw [setLIntegral_const, mul_comm]

/-- **Center-averaging identity, real form** (T9). For a measurable, nonnegative, `P`-periodic
`h : ℝ → ℝ` integrable on `(0, P]` and a measurable set `I` of finite measure,
`∫_{(0,P]} ∫_I h(τ₀ + t) dt dτ₀ = |I| ∫_{(0,P]} h(τ) dτ`. -/
theorem integral_center_average {P : ℝ} (hP : 0 < P) {h : ℝ → ℝ} (hm : Measurable h)
    (h0 : ∀ τ, 0 ≤ h τ) (hper : Function.Periodic h P) (hint : IntegrableOn h (Ioc 0 P))
    {I : Set ℝ} (hI : volume I ≠ ∞) :
    ∫ τ₀ in Ioc 0 P, ∫ t in I, h (τ₀ + t) = volume.real I * ∫ τ in Ioc 0 P, h τ := by
  set g : ℝ → ℝ≥0∞ := fun τ => ENNReal.ofReal (h τ) with hg
  have hgm : Measurable g := ENNReal.measurable_ofReal.comp hm
  have hgper : Function.Periodic g P := fun τ => by simp only [hg, hper τ]
  have hinner : ∀ τ₀, ∫ t in I, h (τ₀ + t) = (∫⁻ t in I, g (τ₀ + t)).toReal := by
    intro τ₀
    have hmeas : Measurable fun t => h (τ₀ + t) := hm.comp (measurable_const_add τ₀)
    rw [integral_eq_lintegral_of_nonneg_ae (f := fun t => h (τ₀ + t))
      (Eventually.of_forall fun t => h0 _) hmeas.aestronglyMeasurable]
  have hper_int : ∫⁻ τ in Ioc 0 P, g τ ≠ ∞ := by
    have := hint.hasFiniteIntegral
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun τ => h0 τ)] at this
    exact this.ne
  have htot := lintegral_center_average hP hgm hgper (I := I)
  have hGm : Measurable fun τ₀ => ∫⁻ t in I, g (τ₀ + t) :=
    (hgm.comp (measurable_fst.add measurable_snd)).lintegral_prod_right'
  have hfin : ∀ᵐ τ₀ ∂(volume.restrict (Ioc 0 P)), ∫⁻ t in I, g (τ₀ + t) < ∞ := by
    refine ae_lt_top' ?_ ?_
    · exact hGm.aemeasurable
    · rw [htot]; exact ENNReal.mul_ne_top hI hper_int
  simp_rw [hinner]
  rw [integral_toReal hGm.aemeasurable hfin, htot, ENNReal.toReal_mul,
    integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun τ => h0 τ)
      hm.aestronglyMeasurable]
  rfl

end UnforcedLeray.BochnerTime
