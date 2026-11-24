import UnforcedLeray.Analysis.WeakDerivative
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Topology.ContinuousMap.ZeroAtInfty

/-!
# `HeatProfileRegularity` helper: classical derivative fields and the target function spaces

Helper module of `Loc/Hyp/HeatProfileRegularity.lean` (hypothesis `HeatProfileRegularity`,
infrastructure INF04, blueprint unit B0710; `paper/main.tex` lines 274–281).

* `d1 A i = ∂ᵢA` and `d2 A i j = ∂ⱼ∂ᵢA`, the classical coordinate derivatives, bounded by the
  norms of `D¹A`, `D²A`, and linear in `A` for `C²` fields;
* the weights `(1 + |y|)^{-m}` lie in `Lᵖ(ℝ³)` when `mp > 3` (`memLp_weight`): `m = 2, p = 3`
  for the gradient (line 278: `∇H_h ∈ L³`) and `m = 3, p = 2` for the Hessian
  (`∇²H_h ∈ L²`);
* distance bounds in `Lᵖ` and `C₀` from pointwise bounds, and continuity from a Lipschitz bound.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Metric
open scoped ContDiff Topology ENNReal

namespace UnforcedLeray.HeatProfileReg

/-- The classical coordinate derivative `∂ᵢA`. -/
def d1 (A : SpatialField) (i : Fin 3) : SpatialField :=
  fun y => fderiv ℝ A y (coordinateVector i)

/-- The classical second coordinate derivative `∂ⱼ∂ᵢA`. -/
def d2 (A : SpatialField) (i j : Fin 3) : SpatialField :=
  fun y => fderiv ℝ (d1 A i) y (coordinateVector j)

theorem norm_coordinateVector (i : Fin 3) : ‖coordinateVector i‖ = 1 := by
  simp [coordinateVector]

theorem d1_contDiff {A : SpatialField} (hA : ContDiff ℝ 2 A) (i : Fin 3) :
    ContDiff ℝ 1 (d1 A i) :=
  (hA.fderiv_right (m := 1) one_add_one_eq_two.le).clm_apply contDiff_const

theorem d2_continuous {A : SpatialField} (hA : ContDiff ℝ 2 A) (i j : Fin 3) :
    Continuous (d2 A i j) :=
  ((d1_contDiff hA i).continuous_fderiv one_ne_zero).clm_apply continuous_const

theorem norm_d1_le (A : SpatialField) (i : Fin 3) (y : Space) :
    ‖d1 A i y‖ ≤ ‖iteratedFDeriv ℝ 1 A y‖ := by
  rw [norm_iteratedFDeriv_one]
  calc ‖d1 A i y‖ ≤ ‖fderiv ℝ A y‖ * ‖coordinateVector i‖ := (fderiv ℝ A y).le_opNorm _
    _ = ‖fderiv ℝ A y‖ := by rw [norm_coordinateVector, mul_one]

theorem d2_apply {A : SpatialField} (hA : ContDiff ℝ 2 A) (i j : Fin 3) (y : Space) :
    d2 A i j y = fderiv ℝ (fderiv ℝ A) y (coordinateVector j) (coordinateVector i) := by
  have hdA : Differentiable ℝ (fderiv ℝ A) :=
    (hA.fderiv_right (m := 1) one_add_one_eq_two.le).differentiable one_ne_zero
  have h := ((hdA y).hasFDerivAt.clm_apply (hasFDerivAt_const (coordinateVector i) y)).fderiv
  show fderiv ℝ (fun y => fderiv ℝ A y (coordinateVector i)) y (coordinateVector j) = _
  rw [h]
  simp

theorem norm_d2_le {A : SpatialField} (hA : ContDiff ℝ 2 A) (i j : Fin 3) (y : Space) :
    ‖d2 A i j y‖ ≤ ‖iteratedFDeriv ℝ 2 A y‖ := by
  have e : ‖fderiv ℝ (fderiv ℝ A) y‖ = ‖iteratedFDeriv ℝ 2 A y‖ := by
    rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
  rw [d2_apply hA, ← e]
  calc ‖fderiv ℝ (fderiv ℝ A) y (coordinateVector j) (coordinateVector i)‖
      ≤ ‖fderiv ℝ (fderiv ℝ A) y‖ * ‖coordinateVector j‖ * ‖coordinateVector i‖ :=
        ContinuousLinearMap.le_opNorm₂ _ _ _
    _ = ‖fderiv ℝ (fderiv ℝ A) y‖ := by rw [norm_coordinateVector, norm_coordinateVector,
        mul_one, mul_one]

theorem d1_sub {A B : SpatialField} (hA : ContDiff ℝ 2 A) (hB : ContDiff ℝ 2 B) (i : Fin 3)
    (y : Space) : d1 (A - B) i y = d1 A i y - d1 B i y := by
  simp only [d1]
  rw [fderiv_sub ((hA.differentiable (by norm_num)) y) ((hB.differentiable (by norm_num)) y)]
  rfl

theorem d2_sub {A B : SpatialField} (hA : ContDiff ℝ 2 A) (hB : ContDiff ℝ 2 B) (i j : Fin 3)
    (y : Space) : d2 (A - B) i j y = d2 A i j y - d2 B i j y := by
  have h1 : d1 (A - B) i = d1 A i - d1 B i := funext fun y => d1_sub hA hB i y
  simp only [d2]
  rw [h1, fderiv_sub (((d1_contDiff hA i).differentiable one_ne_zero) y)
    (((d1_contDiff hB i).differentiable one_ne_zero) y)]
  rfl

/-! ### Weighted Lebesgue spaces -/

/-- `(1 + |y|)^{-m} ∈ Lᵖ(ℝ³)` when `mp > 3`. -/
theorem memLp_weight (m : ℕ) (p : ℝ≥0∞) (hp0 : p ≠ 0) (hpt : p ≠ ⊤)
    (hmp : 3 < (m : ℝ) * p.toReal) :
    MemLp (fun y : Space => ((1 + ‖y‖) ^ m)⁻¹) p volume := by
  have hmeas : AEStronglyMeasurable (fun y : Space => ((1 + ‖y‖) ^ m)⁻¹) volume := by
    have : Measurable (fun y : Space => ((1 + ‖y‖) ^ m)⁻¹) := by fun_prop
    exact this.aestronglyMeasurable
  rw [← integrable_norm_rpow_iff hmeas hp0 hpt]
  have hfin : (Module.finrank ℝ Space : ℝ) = 3 := by simp
  have hint := integrable_one_add_norm (E := Space) (μ := volume) (r := (m : ℝ) * p.toReal)
    (by rw [hfin]; exact hmp)
  refine hint.congr (Eventually.of_forall fun y => ?_)
  have hpos : 0 < 1 + ‖y‖ := by positivity
  show (1 + ‖y‖) ^ (-((m : ℝ) * p.toReal)) = ‖((1 + ‖y‖) ^ m)⁻¹‖ ^ p.toReal
  rw [Real.norm_of_nonneg (by positivity), ← Real.rpow_natCast, ← Real.rpow_neg hpos.le,
    ← Real.rpow_mul hpos.le, neg_mul]

theorem norm_weight (m : ℕ) (y : Space) : ‖((1 + ‖y‖) ^ m)⁻¹‖ = 1 / (1 + ‖y‖) ^ m := by
  rw [Real.norm_of_nonneg (by positivity), one_div]

/-- An `Lᵖ` distance bound from a pointwise bound. -/
theorem dist_toLp_le {p : ℝ≥0∞} {f g : SpatialField} (hf : MemLp f p volume)
    (hg : MemLp g p volume) {w : Space → ℝ} (hw : MemLp w p volume) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ y, ‖f y - g y‖ ≤ c * ‖w y‖) :
    dist (hf.toLp f) (hg.toLp g) ≤ c * (eLpNorm w p volume).toReal := by
  rw [Lp.dist_def]
  have he : (⇑(hf.toLp f) - ⇑(hg.toLp g)) =ᵐ[volume] (f - g) :=
    hf.coeFn_toLp.sub hg.coeFn_toLp
  rw [eLpNorm_congr_ae he]
  have h1 := eLpNorm_le_mul_eLpNorm_of_ae_le_mul (μ := volume) (f := f - g) (g := w) (c := c)
    (Eventually.of_forall h) p
  calc (eLpNorm (f - g) p volume).toReal ≤ (ENNReal.ofReal c * eLpNorm w p volume).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hw.eLpNorm_ne_top) h1
    _ = c * (eLpNorm w p volume).toReal := by rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc]

/-- Decay `c / (1 + |y|)` gives vanishing at infinity. -/
theorem tendsto_zero_of_decay {f : SpatialField} {c : ℝ} (h : ∀ y, ‖f y‖ ≤ c / (1 + ‖y‖)) :
    Tendsto f (cocompact Space) (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h1 : Tendsto (fun y : Space => c / (1 + ‖y‖)) (cocompact Space) (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_left _ 1 (tendsto_norm_cocompact_atTop (E := Space)))
  exact squeeze_zero (fun y => norm_nonneg _) h h1

/-- A `C₀` distance bound from a pointwise bound. -/
theorem dist_C0_le {F G : ZeroAtInftyContinuousMap Space Space} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ y, ‖F y - G y‖ ≤ c) : dist F G ≤ c := by
  rw [← ZeroAtInftyContinuousMap.dist_toBCF_eq_dist, BoundedContinuousFunction.dist_le hc]
  intro y
  rw [dist_eq_norm]
  exact h y

/-- Continuity from a Lipschitz bound in the phase. -/
theorem continuous_of_dist_le {X : Type} [PseudoMetricSpace X] {F : ℝ → X} {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ σ τ, dist (F σ) (F τ) ≤ K * |σ - τ|) : Continuous F :=
  (LipschitzWith.of_dist_le_mul (K := Real.toNNReal K) fun σ τ => by
    rw [Real.coe_toNNReal _ hK, Real.dist_eq]; exact h σ τ).continuous

end UnforcedLeray.HeatProfileReg
