import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Strongly continuous operator families on Bochner functions (INF14 target T7)


target T7 (shared with INF08). Strongly continuous propagators `U(s, t)` act on Bochner
functions of time in every Duhamel formula of the manuscript; for instance the resolvent
`R_μ f(τ) = ∫_0^∞ e^{-μr} S_ν(r) P_σ f(τ - r) dr` of tex 7427–7445 (blueprint unit B0421) and
the Duhamel terms of the evolution-family block (INF08). Only *strong* continuity is assumed:
norm continuity of `t ↦ U t` fails for the heat and Oseen semigroups.

## Main results

* `aestronglyMeasurable_apply`: `t ↦ U t (f t)` is a.e. strongly measurable when `U` is strongly
  continuous and `f` is a.e. strongly measurable;
* `continuousOn_duhamel`: `s ↦ ∫_a^s U(s, t) f(t) dt` is continuous on `[a, b]` for a jointly
  strongly continuous, uniformly bounded propagator on the triangle `a ≤ t ≤ s ≤ b` and `f`
  integrable on `[a, b]`.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped Interval

namespace UnforcedLeray.BochnerTime

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y]
  [NormedSpace ℝ Y]

/-- Strongly measurable version of `aestronglyMeasurable_apply`. -/
theorem stronglyMeasurable_apply {U : ℝ → X →L[ℝ] Y} (hU : ∀ x, Continuous fun t => U t x)
    {f : ℝ → X} (hf : StronglyMeasurable f) : StronglyMeasurable fun t => U t (f t) := by
  induction f, hf using StronglyMeasurable.induction with
  | @ind c s hs =>
    have : (fun t => U t (s.indicator (fun _ => c) t)) = s.indicator fun t => U t c := by
      funext t
      by_cases ht : t ∈ s
      · simp [ht]
      · simp [ht]
    rw [this]
    exact (hU c).stronglyMeasurable.indicator hs
  | @add f g hf hg _ _ ihf ihg =>
    have : (fun t => U t ((f + g) t)) = fun t => U t (f t) + U t (g t) := by
      funext t; simp [map_add]
    rw [this]
    exact ihf.add ihg
  | @lim f g hf hg ihf hlim =>
    refine stronglyMeasurable_of_tendsto atTop ihf ?_
    rw [tendsto_pi_nhds]
    intro t
    exact ((U t).continuous.tendsto _).comp (hlim t)

/-- **Strongly continuous families preserve measurability** (T7). If `t ↦ U t x` is continuous
for every `x` and `f` is a.e. strongly measurable, then `t ↦ U t (f t)` is a.e. strongly
measurable. -/
theorem aestronglyMeasurable_apply {μ : Measure ℝ} {U : ℝ → X →L[ℝ] Y}
    (hU : ∀ x, Continuous fun t => U t x) {f : ℝ → X} (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun t => U t (f t)) μ := by
  refine ⟨fun t => U t (hf.mk f t), stronglyMeasurable_apply hU hf.stronglyMeasurable_mk, ?_⟩
  filter_upwards [hf.ae_eq_mk] with t ht
  rw [ht]

variable [CompleteSpace Y]

/-- **Continuity of Duhamel integrals** (T7). Let `U(s, t)` be bounded operators, jointly
strongly continuous and bounded by `M` on the triangle `a ≤ t ≤ s ≤ b`, and let `f` be integrable
on `[a, b]`. Then `s ↦ ∫_a^s U(s, t) f(t) dt` is continuous on `[a, b]`. -/
theorem continuousOn_duhamel {U : ℝ → ℝ → X →L[ℝ] Y} {a b M : ℝ} {f : ℝ → X}
    (hU : ∀ x, ContinuousOn (fun q : ℝ × ℝ => U q.1 q.2 x) {q | a ≤ q.2 ∧ q.2 ≤ q.1 ∧ q.1 ≤ b})
    (hb : ∀ s t, a ≤ t → t ≤ s → s ≤ b → ‖U s t‖ ≤ M) (hf : IntegrableOn f (Icc a b)) :
    ContinuousOn (fun s => ∫ t in a..s, U s t (f t)) (Icc a b) := by
  set T : Set (ℝ × ℝ) := {q | a ≤ q.2 ∧ q.2 ≤ q.1 ∧ q.1 ≤ b} with hT
  -- the integrand, extended by zero past the diagonal
  set F : ℝ → ℝ → Y := fun s t => (Iic s).indicator (fun t => U s t (f t)) t with hF
  have hrepr : ∀ s ∈ Icc a b, ∫ t in a..s, U s t (f t) = ∫ t in a..b, F s t := by
    intro s hs
    rw [intervalIntegral.integral_of_le hs.1, intervalIntegral.integral_of_le (hs.1.trans hs.2)]
    simp only [hF]
    rw [setIntegral_indicator measurableSet_Iic, Ioc_inter_Iic, min_eq_right hs.2]
  refine ContinuousOn.congr ?_ hrepr
  intro s₀ hs₀
  have hab : a ≤ b := hs₀.1.trans hs₀.2
  have hfI : IntegrableOn f (Ioc a b) := hf.mono_set Ioc_subset_Icc_self
  -- measurability of the slices
  have hmeas : ∀ s ∈ Icc a b, AEStronglyMeasurable (F s) (volume.restrict (Ι a b)) := by
    intro s hs
    set V : ℝ → X →L[ℝ] Y := fun t => U s (max a (min t s)) with hV
    have hVc : ∀ x, Continuous fun t => V t x := by
      intro x
      have hmap : Continuous fun t : ℝ => ((s, max a (min t s)) : ℝ × ℝ) :=
        continuous_const.prodMk (continuous_const.max (continuous_id.min continuous_const))
      refine (hU x).comp_continuous hmap fun t => ?_
      exact ⟨le_max_left _ _, max_le hs.1 (min_le_right _ _), hs.2⟩
    have hVf : AEStronglyMeasurable (fun t => V t (f t)) (volume.restrict (Ι a b)) := by
      rw [uIoc_of_le hab]
      exact aestronglyMeasurable_apply hVc hfI.aestronglyMeasurable
    have hind : AEStronglyMeasurable ((Iic s).indicator fun t => V t (f t))
        (volume.restrict (Ι a b)) := hVf.indicator measurableSet_Iic
    refine hind.congr ?_
    rw [uIoc_of_le hab]
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun t ht => ?_)
    by_cases hts : t ∈ Iic s
    · have hmax : max a (min t s) = t := by
        rw [min_eq_left (show t ≤ s from hts), max_eq_right ht.1.le]
      simp only [hF, indicator_of_mem hts, hV, hmax]
    · simp only [hF, indicator_of_notMem hts]
  -- the dominating function
  set M' := max M 0 with hM'
  have hbound : ∀ s ∈ Icc a b, ∀ᵐ t ∂volume, t ∈ Ι a b → ‖F s t‖ ≤ M' * ‖f t‖ := by
    intro s hs
    refine Eventually.of_forall fun t ht => ?_
    rw [uIoc_of_le hab] at ht
    by_cases hts : t ∈ Iic s
    · simp only [hF, indicator_of_mem hts]
      refine ((U s t).le_opNorm (f t)).trans ?_
      exact mul_le_mul_of_nonneg_right ((hb s t ht.1.le hts hs.2).trans (le_max_left _ _))
        (norm_nonneg _)
    · simp only [hF, indicator_of_notMem hts, norm_zero]
      exact mul_nonneg (le_max_right _ _) (norm_nonneg _)
  have hbi : IntervalIntegrable (fun t => M' * ‖f t‖) volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
    exact hfI.norm.const_mul M'
  -- pointwise continuity in the parameter
  have hcont : ∀ᵐ t ∂volume, t ∈ Ι a b → ContinuousWithinAt (fun s => F s t) (Icc a b) s₀ := by
    have hne : ∀ᵐ t ∂volume, t ≠ s₀ := by simp [ae_iff, measure_singleton]
    filter_upwards [hne] with t hts₀ ht
    rw [uIoc_of_le hab] at ht
    rcases lt_or_gt_of_ne hts₀ with hlt | hgt
    · -- `t < s₀`: eventually `t ≤ s`, and the integrand is `U s t (f t)`
      have hev : ∀ᶠ s in 𝓝[Icc a b] s₀, F s t = U s t (f t) := by
        filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds hlt)] with s hs
        simp only [hF, indicator_of_mem (Set.mem_Iic.2 (le_of_lt (Set.mem_Ioi.1 hs)))]
      refine ContinuousWithinAt.congr_of_eventuallyEq ?_ hev ?_
      · -- continuity of `s ↦ U s t (f t)` within `Icc a b ∩ Ici t` at `s₀`
        have hc : ContinuousWithinAt (fun s => U s t (f t)) (Icc a b ∩ Ici t) s₀ := by
          have hmap : ContinuousWithinAt (fun s : ℝ => ((s, t) : ℝ × ℝ)) (Icc a b ∩ Ici t) s₀ :=
            (continuous_id.prodMk continuous_const).continuousWithinAt
          have hg : ContinuousWithinAt (fun q : ℝ × ℝ => U q.1 q.2 (f t)) T
              ((fun s : ℝ => ((s, t) : ℝ × ℝ)) s₀) :=
            (hU (f t)) (s₀, t) ⟨ht.1.le, hlt.le, hs₀.2⟩
          exact ContinuousWithinAt.comp (f := fun s : ℝ => ((s, t) : ℝ × ℝ)) (x := s₀) hg hmap
            fun s hs =>
            show (s, t) ∈ T from ⟨ht.1.le, Set.mem_Ici.1 hs.2, hs.1.2⟩
        refine (continuousWithinAt_inter' ?_).1 hc
        exact mem_nhdsWithin_of_mem_nhds (Ici_mem_nhds hlt)
      · simp only [hF, indicator_of_mem (Set.mem_Iic.2 hlt.le)]
    · -- `s₀ < t`: eventually `s < t`, and the integrand vanishes
      have hev : ∀ᶠ s in 𝓝[Icc a b] s₀, F s t = 0 := by
        filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds hgt)] with s hs
        simp only [hF, indicator_of_notMem (fun h' => absurd (Set.mem_Iic.1 h') (not_le.2 (Set.mem_Iio.1 hs)))]
      refine ContinuousWithinAt.congr_of_eventuallyEq continuousWithinAt_const hev ?_
      simp only [hF, indicator_of_notMem (fun h' => absurd (Set.mem_Iic.1 h') (not_le.2 hgt))]
  exact intervalIntegral.continuousWithinAt_of_dominated_interval
    (eventually_nhdsWithin_of_forall hmeas) (eventually_nhdsWithin_of_forall hbound) hbi hcont

end UnforcedLeray.BochnerTime
