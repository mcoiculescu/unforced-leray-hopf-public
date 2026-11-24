import UnforcedLeray.Short.PartI.Sub.T02_5

/-!
# Part I, task `PartI:T02/5`: `GammaIntegrableIoi` (the circulation profile is integrable on `(0, ∞)`)

Source of record: `the November 2 reference manuscript`, lines 261-288 (zero
circulation). The statement is `GammaIntegrableIoi` from `Short/PartI/Sub/T02_5.lean`.

Route. Write `Γ = sliceGamma c w` and `m = sliceCurlMean c w`. By `GammaDeriv`, `Γ' = -m`; by
`GammaTendsto`, `Γ → 0` at `+∞`. Hence `Γ(η) = ∫_{(η,∞)} m`, so `‖Γ(η)‖ₑ ≤ ∫_{(η,∞)} ‖m‖ₑ`.
Tonelli on `{0 < η < t}` gives `∫_{(0,∞)} ∫_{(η,∞)} ‖m‖ₑ dη = ∫ t⁺ ‖m(t)‖ₑ dt`, which is finite by
`CurlMeanMoment`, since `|m| ≤ (1 + |t|)|m|` and `t⁺ ≤ 1 + |t|`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec toVec)
open UnforcedLeray.Cyl (Plane)

/-- A primitive `Γ` of `-m` tending to `0` at `+∞` is the tail integral of `m`. -/
theorem gammaIntegrableIoi_integral_repr (Γ m : ℝ → ℝ) (hderiv : ∀ η, HasDerivAt Γ (-m η) η)
    (hlim : Tendsto Γ atTop (𝓝 0)) (hmi : Integrable m) (η : ℝ) :
    ∫ t in Ioi η, m t = Γ η := by
  have hint : IntegrableOn (fun x => -m x) (Ioi η) := hmi.neg.integrableOn
  have key := integral_Ioi_of_hasDerivAt_of_tendsto (f := Γ) (f' := fun x => -m x) (a := η)
    (hderiv η).continuousAt.continuousWithinAt (fun x _ => hderiv x) hint hlim
  simp only [integral_neg] at key
  linarith

/-- Tonelli on `{0 < η < t}`: `∫_{(0,∞)} ∫_{(η,∞)} ‖m‖ₑ dη ≤ ∫ t⁺ ‖m(t)‖ₑ dt`. -/
theorem gammaIntegrableIoi_tonelli (m : ℝ → ℝ) (hmeas : Measurable m) :
    ∫⁻ η in Ioi 0, ∫⁻ t in Ioi η, ‖m t‖ₑ ≤ ∫⁻ t, ENNReal.ofReal t * ‖m t‖ₑ := by
  have hg : Measurable (fun t => ‖m t‖ₑ) := hmeas.enorm
  have hF : Measurable (fun p : ℝ × ℝ => (Ioi p.1).indicator (fun s => ‖m s‖ₑ) p.2) := by
    have hS : MeasurableSet {p : ℝ × ℝ | p.1 < p.2} :=
      measurableSet_lt measurable_fst measurable_snd
    have hfun : (fun p : ℝ × ℝ => (Ioi p.1).indicator (fun s => ‖m s‖ₑ) p.2)
        = {p : ℝ × ℝ | p.1 < p.2}.indicator (fun p => ‖m p.2‖ₑ) := by
      funext p
      by_cases h : p.1 < p.2 <;> simp [h]
    rw [hfun]
    exact Measurable.indicator (hg.comp measurable_snd) hS
  have hinner : ∀ η : ℝ, ∫⁻ t in Ioi η, ‖m t‖ₑ
      = ∫⁻ t, (Ioi η).indicator (fun s => ‖m s‖ₑ) t :=
    fun η => (lintegral_indicator (measurableSet_Ioi : MeasurableSet (Ioi η)) _).symm
  have hout : ∀ t : ℝ, ∫⁻ η in Ioi 0, (Ioi η).indicator (fun s => ‖m s‖ₑ) t
      = ENNReal.ofReal t * ‖m t‖ₑ := by
    intro t
    have h1 : ∫⁻ η in Ioi 0, (Ioi η).indicator (fun s => ‖m s‖ₑ) t
        = ∫⁻ η in Ioi 0, (Iio t).indicator (fun _ => ‖m t‖ₑ) η :=
      lintegral_congr fun η => by
        by_cases h : η < t <;> simp [h]
    rw [h1, lintegral_indicator_const measurableSet_Iio,
      MeasureTheory.Measure.restrict_apply measurableSet_Iio, Set.inter_comm,
      Set.Ioi_inter_Iio, Real.volume_Ioo, sub_zero, mul_comm]
  refine le_of_eq ?_
  calc ∫⁻ η in Ioi 0, ∫⁻ t in Ioi η, ‖m t‖ₑ
      = ∫⁻ η in Ioi 0, ∫⁻ t, (Ioi η).indicator (fun s => ‖m s‖ₑ) t :=
        lintegral_congr fun η => hinner η
    _ = ∫⁻ t, ∫⁻ η in Ioi 0, (Ioi η).indicator (fun s => ‖m s‖ₑ) t :=
        lintegral_lintegral_swap (f := fun η t => (Ioi η).indicator (fun s => ‖m s‖ₑ) t)
          hF.aemeasurable
    _ = ∫⁻ t, ENNReal.ofReal t * ‖m t‖ₑ := lintegral_congr hout

/-- Analytic core: `Γ' = -m`, `Γ → 0` at `+∞`, and `∫ (1 + |t|)|m| < ∞` give
`Γ` integrable on `(0, ∞)`. -/
theorem gammaIntegrableIoi_aux (Γ m : ℝ → ℝ) (hderiv : ∀ η, HasDerivAt Γ (-m η) η)
    (hlim : Tendsto Γ atTop (𝓝 0)) (hmom : Integrable (fun t : ℝ => (1 + |t|) * |m t|)) :
    IntegrableOn Γ (Ioi 0) := by
  have hΓc : Continuous Γ := continuous_iff_continuousAt.2 fun η => (hderiv η).continuousAt
  have hm_eq : m = fun t => -deriv Γ t := by
    funext t
    rw [(hderiv t).deriv, neg_neg]
  have hmeas : Measurable m := by
    rw [hm_eq]
    exact (measurable_deriv Γ).neg
  have hmi : Integrable m := by
    refine Integrable.mono' hmom hmeas.aestronglyMeasurable (ae_of_all _ fun t => ?_)
    show ‖m t‖ ≤ (1 + |t|) * |m t|
    rw [Real.norm_eq_abs]
    nlinarith [mul_nonneg (abs_nonneg t) (abs_nonneg (m t))]
  have hbound : ∀ η, ‖Γ η‖ₑ ≤ ∫⁻ t in Ioi η, ‖m t‖ₑ := by
    intro η
    rw [← gammaIntegrableIoi_integral_repr Γ m hderiv hlim hmi η]
    exact enorm_integral_le_lintegral_enorm m
  have hpt : ∀ t : ℝ, ENNReal.ofReal t * ‖m t‖ₑ ≤ ‖(1 + |t|) * |m t|‖ₑ := by
    intro t
    rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs,
      abs_of_nonneg (show (0 : ℝ) ≤ (1 + |t|) * |m t| by positivity),
      ENNReal.ofReal_mul (show (0 : ℝ) ≤ 1 + |t| by positivity)]
    exact mul_le_mul_of_nonneg_right
      (ENNReal.ofReal_le_ofReal (by linarith [le_abs_self t])) zero_le
  have hfin : ∫⁻ t, ENNReal.ofReal t * ‖m t‖ₑ < ⊤ :=
    lt_of_le_of_lt (lintegral_mono hpt) (hasFiniteIntegral_iff_enorm.1 hmom.2)
  refine ⟨hΓc.aestronglyMeasurable, hasFiniteIntegral_iff_enorm.2 ?_⟩
  calc ∫⁻ η in Ioi 0, ‖Γ η‖ₑ ≤ ∫⁻ η in Ioi 0, ∫⁻ t in Ioi η, ‖m t‖ₑ :=
        lintegral_mono fun η => hbound η
    _ ≤ ∫⁻ t, ENNReal.ofReal t * ‖m t‖ₑ := gammaIntegrableIoi_tonelli m hmeas
    _ < ⊤ := hfin

/-- **`PartI:T02/5`, `GammaIntegrableIoi`**: the circulation profile `Γ` of a slice is integrable
on `(0, ∞)`, from `GammaDeriv`, `GammaTendsto` and `CurlMeanMoment`. -/
theorem gammaIntegrableIoi (h6 : GammaDeriv) (h8 : GammaTendsto) (h9 : CurlMeanMoment) :
    GammaIntegrableIoi := by
  intro c w hs
  exact gammaIntegrableIoi_aux (sliceGamma c w) (sliceCurlMean c w) (h6 c w hs)
    (h8 c w hs).1 (h9 c w hs)

end UnforcedLeray.Short.PartI
