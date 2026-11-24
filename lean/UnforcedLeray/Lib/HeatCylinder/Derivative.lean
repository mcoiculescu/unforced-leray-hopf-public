import UnforcedLeray.Lib.HeatCylinder.Linearity
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Differentiating the actual Gaussian heat-divergence convolution

This module uses Mathlib's dominated differentiation theorem on the explicit B0296 Gaussian
kernel. The theorem below gives directional derivative commutation for bounded `C¹` inputs with a
uniformly bounded directional derivative; these hypotheses are met by smooth periodic fields with
compact axial support.
-/

set_option autoImplicit false
set_option maxHeartbeats 500000

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.GaussianVortex (Plane)

/-- The Gaussian divergence kernel, packaged as a continuous linear map in the tensor variable. -/
def divKernelCLM (θ : ℝ) (w : Plane) : (Plane × Plane) →L[ℝ] Plane :=
  (UnforcedLeray.B0296.gradHeatKernel2 θ w).1 • ContinuousLinearMap.fst ℝ Plane Plane +
    (UnforcedLeray.B0296.gradHeatKernel2 θ w).2 • ContinuousLinearMap.snd ℝ Plane Plane

@[simp] theorem divKernelCLM_apply (θ : ℝ) (w : Plane) (x : Plane × Plane) :
    divKernelCLM θ w x = UnforcedLeray.B0296.divKernel θ w x := by
  simp [divKernelCLM, UnforcedLeray.B0296.divKernel]


/-- The operator norm of the actual divergence kernel is bounded by the sum of the absolute
Gaussian gradient components used by its integrable envelope. -/
theorem divKernelCLM_norm_le (θ : ℝ) (w : Plane) :
    ‖divKernelCLM θ w‖ ≤ (UnforcedLeray.B0296.gradKernelAbs θ w).toReal := by
  apply ContinuousLinearMap.opNorm_le_bound _ (ENNReal.toReal_nonneg)
  intro x
  have h := UnforcedLeray.B0296.enorm_divKernel_le θ w x
  have hk : UnforcedLeray.B0296.gradKernelAbs θ w ≠ ∞ :=
    UnforcedLeray.B0296.gradKernelAbs_ne_top θ w
  have htop : UnforcedLeray.B0296.gradKernelAbs θ w * ‖x‖ₑ ≠ ∞ :=
    ENNReal.mul_ne_top hk enorm_ne_top
  have hr := ENNReal.toReal_mono htop h
  rw [ENNReal.toReal_mul, toReal_enorm, toReal_enorm] at hr
  simpa only [divKernelCLM_apply] using hr


/-- The full Fréchet derivative of the actual Gaussian-divergence convolution is obtained by
integrating the derivative of its translated input. The uniform `C¹` bounds provide the exact
integrable Gaussian-gradient majorant. -/
theorem hasFDerivAt_heatDiv {θ : ℝ} (hθ : 0 < θ)
    {T : Plane → Plane × Plane} (hT : ContDiff ℝ 1 T)
    {M₀ M₁ : ℝ} (hTbound : ∀ x, ‖T x‖ ≤ M₀)
    (hderivBound : ∀ x, ‖fderiv ℝ T x‖ ≤ M₁) (z : Plane) :
    HasFDerivAt (UnforcedLeray.B0296.heatDiv θ T)
      (∫ w : Plane, (divKernelCLM θ w).comp (fderiv ℝ T (z - w))) z := by
  let F : Plane → Plane → Plane := fun z' w =>
    UnforcedLeray.B0296.divKernel θ w (T (z' - w))
  let F' : Plane → Plane → Plane →L[ℝ] Plane := fun z' w =>
    (divKernelCLM θ w).comp (fderiv ℝ T (z' - w))
  let k : Plane → ℝ≥0∞ := UnforcedLeray.B0296.gradKernelAbs θ
  have hmass : (∫⁻ w : Plane, k w) ≠ ∞ := by
    rw [UnforcedLeray.B0296.lintegral_gradKernelAbs hθ]
    exact ENNReal.ofReal_ne_top
      (r := 4 * (Real.sqrt (4 * Real.pi * 1 * θ))⁻¹)
  have hkmeas : Measurable k := UnforcedLeray.B0296.measurable_gradKernelAbs θ
  have hkfinite : ∀ w, k w ≠ ∞ := UnforcedLeray.B0296.gradKernelAbs_ne_top θ
  have hkernelReal : Integrable (fun w : Plane => (k w).toReal) := by
    refine ⟨hkmeas.ennreal_toReal.aestronglyMeasurable, ?_⟩
    change ∫⁻ w : Plane, ‖(k w).toReal‖ₑ < ∞
    have hnorm : (fun w : Plane => ‖(k w).toReal‖ₑ) = k := by
      funext w
      rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (ENNReal.toReal_nonneg),
        ENNReal.ofReal_toReal (hkfinite w)]
    rw [hnorm, UnforcedLeray.B0296.lintegral_gradKernelAbs hθ]
    exact ENNReal.ofReal_lt_top
  have hFmeas : ∀ᶠ z' : Plane in 𝓝 z,
      AEStronglyMeasurable (F z') volume := by
    filter_upwards [] with z'
    exact UnforcedLeray.B0296.aestronglyMeasurable_divIntegrand θ
      hT.continuous.aestronglyMeasurable z'
  have hFint : Integrable (F z) volume := by
    apply UnforcedLeray.B0296.integrable_kconv_of_lt_top
      (A := UnforcedLeray.B0296.divKernel θ) (k := k)
      (UnforcedLeray.B0296.enorm_divKernel_le θ) z
      (UnforcedLeray.B0296.aestronglyMeasurable_divIntegrand θ
        hT.continuous.aestronglyMeasurable z)
    have hmajor : ∫⁻ w : Plane, k w * ‖T (z - w)‖ₑ ≤
        (∫⁻ w : Plane, k w) * ENNReal.ofReal M₀ := by
      calc
        ∫⁻ w : Plane, k w * ‖T (z - w)‖ₑ ≤
            ∫⁻ w : Plane, k w * ENNReal.ofReal M₀ :=
          lintegral_mono fun w => by
            have hTnn : ‖T (z - w)‖ₑ ≤ ENNReal.ofReal M₀ := by
              rw [← ofReal_norm]
              exact ENNReal.ofReal_le_ofReal (hTbound _)
            exact mul_le_mul_of_nonneg_left hTnn bot_le
        _ = (∫⁻ w : Plane, k w) * ENNReal.ofReal M₀ := by
          rw [lintegral_mul_const _ hkmeas]
    exact (hmajor.trans_lt (ENNReal.mul_ne_top hmass
      (ENNReal.ofReal_ne_top (r := M₀))).lt_top)
  have hFprimeMeas : AEStronglyMeasurable (F' z) volume := by
    have hder : Continuous (fun w : Plane => fderiv ℝ T (z - w)) := by
      exact (hT.continuous_fderiv one_ne_zero).comp
        (continuous_const.sub continuous_id)
    have hgrad₁ : Continuous (fun w : Plane => (UnforcedLeray.B0296.gradHeatKernel2 θ w).1) := by
      unfold UnforcedLeray.B0296.gradHeatKernel2
      exact ((UnforcedLeray.B0296.continuous_dHeatKernel θ).comp continuous_fst).mul
        ((UnforcedLeray.B0296.continuous_heatKernel1 θ).comp continuous_snd)
    have hgrad₂ : Continuous (fun w : Plane => (UnforcedLeray.B0296.gradHeatKernel2 θ w).2) := by
      unfold UnforcedLeray.B0296.gradHeatKernel2
      exact ((UnforcedLeray.B0296.continuous_heatKernel1 θ).comp continuous_fst).mul
        ((UnforcedLeray.B0296.continuous_dHeatKernel θ).comp continuous_snd)
    have hker : Continuous (fun w : Plane => divKernelCLM θ w) := by
      unfold divKernelCLM
      exact hgrad₁.smul continuous_const |>.add (hgrad₂.smul continuous_const)
    exact (hker.clm_comp hder).measurable.aestronglyMeasurable
  have hbound : ∀ᵐ w ∂(volume : Measure Plane), ∀ z' ∈ Metric.ball z 1,
      ‖F' z' w‖ ≤ (k w).toReal * M₁ := by
    filter_upwards [] with w
    intro z' hz'
    calc
      ‖(divKernelCLM θ w).comp (fderiv ℝ T (z' - w))‖ ≤
          ‖divKernelCLM θ w‖ * ‖fderiv ℝ T (z' - w)‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (k w).toReal * M₁ := by
        exact mul_le_mul (divKernelCLM_norm_le θ w) (hderivBound _)
          (norm_nonneg _) ENNReal.toReal_nonneg
  have hboundInt : Integrable (fun w : Plane => (k w).toReal * M₁) :=
    hkernelReal.mul_const M₁
  have hdiff : ∀ᵐ w ∂(volume : Measure Plane), ∀ z' ∈ Metric.ball z 1,
      HasFDerivAt (F · w) (F' z' w) z' := by
    filter_upwards [] with w
    intro z' hz'
    have hinput : HasFDerivAt (fun y : Plane => y - w)
        (ContinuousLinearMap.id ℝ Plane) z' := (hasFDerivAt_id z').sub_const w
    have hTloc : ContDiffAt ℝ 1 T (z' - w) := hT.contDiffAt
    have hTcomp := (hTloc.differentiableAt one_ne_zero).hasFDerivAt.comp z' hinput
    have hcomp := (divKernelCLM θ w).hasFDerivAt.comp z' hTcomp
    convert hcomp using 1
    all_goals rfl
  have hparam := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (s := Metric.ball z 1) (x₀ := z) (μ := (volume : Measure Plane))
    (F := F) (F' := F') (bound := fun w => (k w).toReal * M₁)
    (Metric.ball_mem_nhds z one_pos) hFmeas hFint hFprimeMeas hbound hboundInt hdiff
  have hfun : (fun z' : Plane => UnforcedLeray.B0296.heatDiv θ T z') =
      fun z' => ∫ w : Plane, F z' w := by
    funext z'
    rw [UnforcedLeray.B0296.heatDiv_apply_of_pos hθ]
  exact hparam.congr_of_eventuallyEq (Eventually.of_forall (congrFun hfun))


/-- Evaluating the Fréchet derivative of heatDiv on a direction gives the actual convolution of
the directional derivative of the tensor field. -/
theorem heatDivFDeriv_apply {θ : ℝ} (hθ : 0 < θ)
    {T : Plane → Plane × Plane} (hT : ContDiff ℝ 1 T)
    {M₁ : ℝ} (hderivBound : ∀ x, ‖fderiv ℝ T x‖ ≤ M₁) (z e : Plane) :
    (∫ w : Plane, (divKernelCLM θ w).comp (fderiv ℝ T (z - w))) e =
      UnforcedLeray.B0296.heatDiv θ (fun x => fderiv ℝ T x e) z := by
  let J : Plane → Plane →L[ℝ] Plane := fun w =>
    (divKernelCLM θ w).comp (fderiv ℝ T (z - w))
  have hmass : (∫⁻ w : Plane, UnforcedLeray.B0296.gradKernelAbs θ w) ≠ ∞ := by
    rw [UnforcedLeray.B0296.lintegral_gradKernelAbs hθ]
    exact ENNReal.ofReal_ne_top
      (r := 4 * (Real.sqrt (4 * Real.pi * 1 * θ))⁻¹)
  have hkernelReal : Integrable
      (fun w : Plane => (UnforcedLeray.B0296.gradKernelAbs θ w).toReal) := by
    have hkmeas : Measurable (fun w : Plane => UnforcedLeray.B0296.gradKernelAbs θ w) :=
      UnforcedLeray.B0296.measurable_gradKernelAbs θ
    have hkfinite : ∀ w, UnforcedLeray.B0296.gradKernelAbs θ w ≠ ∞ :=
      UnforcedLeray.B0296.gradKernelAbs_ne_top θ
    refine ⟨hkmeas.ennreal_toReal.aestronglyMeasurable, ?_⟩
    change ∫⁻ w : Plane,
      ‖(UnforcedLeray.B0296.gradKernelAbs θ w).toReal‖ₑ < ∞
    have hnorm : (fun w : Plane =>
        ‖(UnforcedLeray.B0296.gradKernelAbs θ w).toReal‖ₑ) =
          fun w => UnforcedLeray.B0296.gradKernelAbs θ w := by
      funext w
      rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (ENNReal.toReal_nonneg),
        ENNReal.ofReal_toReal (hkfinite w)]
    rw [hnorm, UnforcedLeray.B0296.lintegral_gradKernelAbs hθ]
    exact ENNReal.ofReal_lt_top
  have hker : Continuous (fun w : Plane => divKernelCLM θ w) := by
    have hgrad₁ : Continuous (fun w : Plane => (UnforcedLeray.B0296.gradHeatKernel2 θ w).1) := by
      unfold UnforcedLeray.B0296.gradHeatKernel2
      exact ((UnforcedLeray.B0296.continuous_dHeatKernel θ).comp continuous_fst).mul
        ((UnforcedLeray.B0296.continuous_heatKernel1 θ).comp continuous_snd)
    have hgrad₂ : Continuous (fun w : Plane => (UnforcedLeray.B0296.gradHeatKernel2 θ w).2) := by
      unfold UnforcedLeray.B0296.gradHeatKernel2
      exact ((UnforcedLeray.B0296.continuous_heatKernel1 θ).comp continuous_fst).mul
        ((UnforcedLeray.B0296.continuous_dHeatKernel θ).comp continuous_snd)
    unfold divKernelCLM
    exact hgrad₁.smul continuous_const |>.add (hgrad₂.smul continuous_const)
  have hder : Continuous (fun w : Plane => fderiv ℝ T (z - w)) := by
    exact (hT.continuous_fderiv one_ne_zero).comp (continuous_const.sub continuous_id)
  have hJmeas : AEStronglyMeasurable J volume :=
    (hker.clm_comp hder).aestronglyMeasurable
  have hM₁ : 0 ≤ M₁ := (norm_nonneg _).trans (hderivBound 0)
  have hJbound : ∀ᵐ w ∂(volume : Measure Plane),
      ‖J w‖ ≤ (UnforcedLeray.B0296.gradKernelAbs θ w).toReal * M₁ := by
    filter_upwards [] with w
    dsimp [J]
    calc
      ‖(divKernelCLM θ w).comp (fderiv ℝ T (z - w))‖ ≤
          ‖divKernelCLM θ w‖ * ‖fderiv ℝ T (z - w)‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (UnforcedLeray.B0296.gradKernelAbs θ w).toReal * M₁ :=
        mul_le_mul (divKernelCLM_norm_le θ w) (hderivBound _)
          (norm_nonneg _) (ENNReal.toReal_nonneg)
  have hJint : Integrable J :=
    Integrable.mono' (hkernelReal.mul_const M₁) hJmeas hJbound
  rw [ContinuousLinearMap.integral_apply hJint]
  have hEq : (fun w : Plane => J w e) = fun w =>
      UnforcedLeray.B0296.divKernel θ w (fderiv ℝ T (z - w) e) := by
    funext w
    simp [J, divKernelCLM_apply, UnforcedLeray.B0296.divKernel]
  rw [hEq, UnforcedLeray.B0296.heatDiv_apply_of_pos hθ]

/-- Differentiation under the actual Gaussian-divergence integral commutes with a spatial
translation direction. Explicit uniform bounds on the field and its directional derivative make
the Gaussian majorants integrable. -/
theorem hasDerivAt_heatDiv_direction {θ : ℝ} (hθ : 0 < θ)
    {T : Plane → Plane × Plane} (hT : ContDiff ℝ 1 T)
    {M₀ M₁ : ℝ} (hM₁ : 0 ≤ M₁)
    (hTbound : ∀ x, ‖T x‖ ≤ M₀) (e z : Plane)
    (hderivBound : ∀ x, ‖fderiv ℝ T x e‖ ≤ M₁) :
    HasDerivAt (fun r : ℝ => UnforcedLeray.B0296.heatDiv θ T (z + r • e))
      (UnforcedLeray.B0296.heatDiv θ (fun x => fderiv ℝ T x e) z) 0 := by
  let F : ℝ → Plane → Plane := fun r w =>
    UnforcedLeray.B0296.divKernel θ w (T (z + r • e - w))
  let F' : ℝ → Plane → ℝ →L[ℝ] Plane := fun r w =>
    ContinuousLinearMap.toSpanSingleton ℝ
      (UnforcedLeray.B0296.divKernel θ w (fderiv ℝ T (z + r • e - w) e))
  let k : Plane → ℝ≥0∞ := UnforcedLeray.B0296.gradKernelAbs θ
  have hmass : (∫⁻ w : Plane, k w) ≠ ∞ := by
    rw [UnforcedLeray.B0296.lintegral_gradKernelAbs hθ]
    exact ENNReal.ofReal_ne_top
      (r := 4 * (Real.sqrt (4 * Real.pi * 1 * θ))⁻¹)
  have hkmeas : Measurable k := UnforcedLeray.B0296.measurable_gradKernelAbs θ
  have hkfinite : ∀ w, k w ≠ ∞ := UnforcedLeray.B0296.gradKernelAbs_ne_top θ
  have hkernelReal : Integrable (fun w : Plane => (k w).toReal) := by
    refine ⟨hkmeas.ennreal_toReal.aestronglyMeasurable, ?_⟩
    change ∫⁻ w : Plane, ‖(k w).toReal‖ₑ < ∞
    have hnorm : (fun w : Plane => ‖(k w).toReal‖ₑ) = k := by
      funext w
      rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (ENNReal.toReal_nonneg),
        ENNReal.ofReal_toReal (hkfinite w)]
    rw [hnorm, UnforcedLeray.B0296.lintegral_gradKernelAbs hθ]
    exact ENNReal.ofReal_lt_top
  have hFmeas : ∀ᶠ r : ℝ in 𝓝 (0 : ℝ), AEStronglyMeasurable (F r) volume := by
    filter_upwards [] with r
    exact UnforcedLeray.B0296.aestronglyMeasurable_divIntegrand θ
      hT.continuous.aestronglyMeasurable (z + r • e)
  have hFint : Integrable (F 0) volume := by
    apply UnforcedLeray.B0296.integrable_kconv_of_lt_top
      (A := UnforcedLeray.B0296.divKernel θ) (k := k)
      (UnforcedLeray.B0296.enorm_divKernel_le θ) (z + (0 : ℝ) • e)
      (UnforcedLeray.B0296.aestronglyMeasurable_divIntegrand θ
        hT.continuous.aestronglyMeasurable (z + (0 : ℝ) • e))
    have hmajor : ∫⁻ w : Plane, k w * ‖T (z + (0 : ℝ) • e - w)‖ₑ ≤
        (∫⁻ w : Plane, k w) * ENNReal.ofReal M₀ := by
      calc
        ∫⁻ w : Plane, k w * ‖T (z + (0 : ℝ) • e - w)‖ₑ ≤
            ∫⁻ w : Plane, k w * ENNReal.ofReal M₀ :=
          lintegral_mono fun w => by
            have hTnn : ‖T (z + (0 : ℝ) • e - w)‖ₑ ≤ ENNReal.ofReal M₀ := by
              rw [← ofReal_norm]
              exact ENNReal.ofReal_le_ofReal (hTbound _)
            exact mul_le_mul_of_nonneg_left hTnn bot_le
        _ = (∫⁻ w : Plane, k w) * ENNReal.ofReal M₀ := by
          rw [lintegral_mul_const _ hkmeas]
    exact (hmajor.trans_lt (ENNReal.mul_ne_top hmass
      (ENNReal.ofReal_ne_top (r := M₀))).lt_top)
  have hFprimeMeas : AEStronglyMeasurable (F' 0) volume := by
    have hder : Measurable (fun w : Plane => fderiv ℝ T (z + (0 : ℝ) • e - w) e) := by
      have harg : Measurable (fun w : Plane => z + (0 : ℝ) • e - w) := by fun_prop
      have hdf : Measurable (fun w : Plane => fderiv ℝ T (z + (0 : ℝ) • e - w)) :=
        (hT.continuous_fderiv one_ne_zero).measurable.comp harg
      exact (continuous_eval_const e).measurable.comp hdf
    have hvec : Measurable (fun w : Plane =>
        UnforcedLeray.B0296.divKernel θ w (fderiv ℝ T (z + (0 : ℝ) • e - w) e)) := by
      exact UnforcedLeray.HeatCylinder.measurable_divKernel_param.comp
        (measurable_const.prodMk (measurable_id.prodMk hder))
    have hspan : Continuous (fun v : Plane =>
        ContinuousLinearMap.toSpanSingleton ℝ v) :=
      (ContinuousLinearMap.toSpanSingletonCLE (𝕜 := ℝ) (E := Plane)).continuous
    have hvec' : AEStronglyMeasurable
        (fun w : Plane => UnforcedLeray.B0296.divKernel θ w
          (fderiv ℝ T (z + (0 : ℝ) • e - w) e)) volume := hvec.aestronglyMeasurable
    exact hspan.comp_aestronglyMeasurable hvec'
  have hbound : ∀ᵐ w ∂(volume : Measure Plane), ∀ r ∈ Set.univ,
      ‖F' r w‖ ≤ (k w).toReal * M₁ := by
    filter_upwards [] with w
    intro r _
    have hkernel := UnforcedLeray.B0296.enorm_divKernel_le θ w
      (fderiv ℝ T (z + r • e - w) e)
    have hdernorm : ‖fderiv ℝ T (z + r • e - w) e‖ₑ ≤ ENNReal.ofReal M₁ := by
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hderivBound _)
    have hprod : ‖UnforcedLeray.B0296.divKernel θ w
        (fderiv ℝ T (z + r • e - w) e)‖ₑ ≤ k w * ENNReal.ofReal M₁ :=
      hkernel.trans (mul_le_mul_of_nonneg_left hdernorm bot_le)
    have htop : k w * ENNReal.ofReal M₁ ≠ ∞ :=
      ENNReal.mul_ne_top (hkfinite w) (ENNReal.ofReal_ne_top (r := M₁))
    have hreal := ENNReal.toReal_mono htop hprod
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hM₁] at hreal
    simpa [F', ContinuousLinearMap.norm_toSpanSingleton,
      ENNReal.toReal_ofReal (norm_nonneg _)] using hreal
  have hboundInt : Integrable (fun w : Plane => (k w).toReal * M₁) :=
    hkernelReal.mul_const M₁
  have hdiff : ∀ᵐ w ∂(volume : Measure Plane), ∀ r ∈ Set.univ,
      HasFDerivAt (F · w) (F' r w) r := by
    filter_upwards [] with w
    intro r _
    have hinput : HasFDerivAt (fun r : ℝ => z + r • e - w)
        (ContinuousLinearMap.toSpanSingleton ℝ e) r := by
      convert (((hasFDerivAt_id r).smul_const e).const_add z).sub_const w using 1
      all_goals rfl
    have hTloc : ContDiffAt ℝ 1 T (z + r • e - w) := hT.contDiffAt
    have hTcomp := hTloc.differentiableAt_one.hasFDerivAt.comp r hinput
    have hcomp := (divKernelCLM θ w).hasFDerivAt.comp r hTcomp
    convert hcomp using 1
    all_goals first | rfl | (rw [← ContinuousLinearMap.comp_assoc,
      ContinuousLinearMap.comp_toSpanSingleton]; simp [F', divKernelCLM_apply])
  have hparam := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (s := Set.univ) (x₀ := (0 : ℝ)) (μ := (volume : Measure Plane))
    (F := F) (F' := F') (bound := fun w => (k w).toReal * M₁)
    Filter.univ_mem hFmeas hFint hFprimeMeas hbound hboundInt hdiff
  have hfun : (fun r : ℝ => UnforcedLeray.B0296.heatDiv θ T (z + r • e)) =
      fun r => ∫ w : Plane, F r w := by
    funext r
    rw [UnforcedLeray.B0296.heatDiv_apply_of_pos hθ]
  have hparam' := hparam.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun r => congrFun hfun r)
  have hderiv : (∫ w : Plane, F' 0 w) =
      ContinuousLinearMap.toSpanSingleton ℝ
        (UnforcedLeray.B0296.heatDiv θ (fun x => fderiv ℝ T x e) z) := by
    apply ContinuousLinearMap.ext
    intro a
    have hbound0 : ∀ᵐ w ∂(volume : Measure Plane),
        ‖F' 0 w‖ ≤ (k w).toReal * M₁ :=
      hbound.mono fun w hw => hw 0 (Set.mem_univ 0)
    have hF'Int : Integrable (F' 0) := Integrable.mono' hboundInt hFprimeMeas hbound0
    rw [ContinuousLinearMap.integral_apply hF'Int]
    change (∫ w : Plane, a • UnforcedLeray.B0296.divKernel θ w
        (fderiv ℝ T (z + (0 : ℝ) • e - w) e)) =
      a • UnforcedLeray.B0296.heatDiv θ (fun x => fderiv ℝ T x e) z
    rw [integral_smul a, UnforcedLeray.B0296.heatDiv_apply_of_pos hθ]
    simp [zero_smul]
  rw [hderiv] at hparam'
  simpa using hparam'.hasDerivAt

end UnforcedLeray.HeatCylinder

#print axioms UnforcedLeray.HeatCylinder.divKernelCLM_norm_le
#print axioms UnforcedLeray.HeatCylinder.hasFDerivAt_heatDiv
#print axioms UnforcedLeray.HeatCylinder.heatDivFDeriv_apply
#print axioms UnforcedLeray.HeatCylinder.hasDerivAt_heatDiv_direction
