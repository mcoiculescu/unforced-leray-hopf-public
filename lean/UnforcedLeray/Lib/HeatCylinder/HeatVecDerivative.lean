import UnforcedLeray.Lib.HeatCylinder.HeatVecConvolution
import UnforcedLeray.Lib.HeatCylinder.SmoothBounds
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Differentiating the actual Euclidean-vector Gaussian heat convolution

For smooth periodic compact-axial inputs, differentiation under the literal B0284 Gaussian
integral is justified by the integrable kernel and the global derivative bound. This gives the
actual classical derivative field needed to build the centered H³ heat output.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.Train (Vec)
open UnforcedLeray.B0284 (heatKernel2)

/-- The scalar Gaussian kernel as an operator on Euclidean-vector values. -/
def heatVecKernelCLM (θ : ℝ) (w : Plane) : Vec →L[ℝ] Vec :=
  heatKernel2 θ w • ContinuousLinearMap.id ℝ Vec

@[simp] theorem heatVecKernelCLM_apply (θ : ℝ) (w : Plane) (x : Vec) :
    heatVecKernelCLM θ w x = heatKernel2 θ w • x := by
  simp [heatVecKernelCLM]

theorem norm_heatVecKernelCLM_le {θ : ℝ} (hθ : 0 < θ) (w : Plane) :
    ‖heatVecKernelCLM θ w‖ ≤ heatKernel2 θ w := by
  rw [heatVecKernelCLM, norm_smul, ContinuousLinearMap.norm_id, mul_one,
    Real.norm_eq_abs,
    abs_of_nonneg (UnforcedLeray.B0284.heatKernel2_nonneg hθ w)]

private theorem continuous_heatKernel2_right {θ : ℝ} (hθ : 0 < θ) :
    Continuous (heatKernel2 θ) := by
  unfold UnforcedLeray.B0284.heatKernel2 UnforcedLeray.B0191.heatKernel
  fun_prop

private theorem continuous_heatVecKernelCLM {θ : ℝ} (hθ : 0 < θ) :
    Continuous (heatVecKernelCLM θ) := by
  unfold heatVecKernelCLM
  exact (continuous_heatKernel2_right hθ).smul continuous_const

/-- Fréchet differentiation under the actual Euclidean-vector Gaussian convolution. -/
theorem hasFDerivAt_heatVecConvolution {θ : ℝ} (hθ : 0 < θ)
    {T : Plane → Vec} (hT : ContDiff ℝ 1 T)
    {M₀ M₁ : ℝ} (hTbound : ∀ x, ‖T x‖ ≤ M₀)
    (hderivBound : ∀ x, ‖fderiv ℝ T x‖ ≤ M₁) (z : Plane) :
    HasFDerivAt (heatVecConvolution θ T)
      (∫ w : Plane, (heatVecKernelCLM θ w).comp (fderiv ℝ T (z - w))) z := by
  let F : Plane → Plane → Vec := fun z' w =>
    heatVecKernelCLM θ w (T (z' - w))
  let F' : Plane → Plane → Plane →L[ℝ] Vec := fun z' w =>
    (heatVecKernelCLM θ w).comp (fderiv ℝ T (z' - w))
  have hkernel : Integrable (heatKernel2 θ) := UnforcedLeray.B0284.integrable_heatKernel2 hθ
  have hkernelCLM : Continuous (heatVecKernelCLM θ) := continuous_heatVecKernelCLM hθ
  have hFcont (z' : Plane) : Continuous (F z') := by
    have hinput : Continuous (fun w : Plane => T (z' - w)) :=
      hT.continuous.comp (continuous_const.sub continuous_id)
    exact hkernelCLM.clm_apply hinput
  have hFmeas : ∀ᶠ z' : Plane in 𝓝 z, AEStronglyMeasurable (F z') volume := by
    exact Filter.Eventually.of_forall fun z' => (hFcont z').aestronglyMeasurable
  have hFint : Integrable (F z) volume := by
    refine Integrable.mono' (hkernel.mul_const M₀) (hFcont z).aestronglyMeasurable ?_
    · filter_upwards [] with w
      change ‖heatVecKernelCLM θ w (T (z - w))‖ ≤ heatKernel2 θ w * M₀
      calc
        ‖heatVecKernelCLM θ w (T (z - w))‖ ≤
            ‖heatVecKernelCLM θ w‖ * ‖T (z - w)‖ :=
          (heatVecKernelCLM θ w).le_opNorm _
        _ ≤ heatKernel2 θ w * M₀ := by
          exact mul_le_mul (norm_heatVecKernelCLM_le hθ w) (hTbound (z - w))
            (norm_nonneg _) (UnforcedLeray.B0284.heatKernel2_nonneg hθ w)
  have hFprimeMeas : AEStronglyMeasurable (F' z) volume := by
    have hder : Continuous (fun w : Plane => fderiv ℝ T (z - w)) :=
      (hT.continuous_fderiv one_ne_zero).comp (continuous_const.sub continuous_id)
    exact (hkernelCLM.clm_comp hder).measurable.aestronglyMeasurable
  have hbound : ∀ᵐ w ∂(volume : Measure Plane), ∀ z' ∈ Metric.ball z 1,
      ‖F' z' w‖ ≤ heatKernel2 θ w * M₁ := by
    filter_upwards [] with w
    intro z' hz'
    calc
      ‖(heatVecKernelCLM θ w).comp (fderiv ℝ T (z' - w))‖ ≤
          ‖heatVecKernelCLM θ w‖ * ‖fderiv ℝ T (z' - w)‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ heatKernel2 θ w * M₁ := by
        exact mul_le_mul (norm_heatVecKernelCLM_le hθ w) (hderivBound (z' - w))
          (norm_nonneg _) (UnforcedLeray.B0284.heatKernel2_nonneg hθ w)
  have hboundInt : Integrable (fun w : Plane => heatKernel2 θ w * M₁) :=
    hkernel.mul_const M₁
  have hFprimeInt : Integrable (F' z) volume := by
    refine Integrable.mono' hboundInt hFprimeMeas ?_
    exact hbound.mono fun w hw => hw z (Metric.mem_ball_self one_pos)
  have hdiff : ∀ᵐ w ∂(volume : Measure Plane), ∀ z' ∈ Metric.ball z 1,
      HasFDerivAt (F · w) (F' z' w) z' := by
    filter_upwards [] with w
    intro z' hz'
    have hinput : HasFDerivAt (fun y : Plane => y - w)
        (ContinuousLinearMap.id ℝ Plane) z' := (hasFDerivAt_id z').sub_const w
    have hTloc : ContDiffAt ℝ 1 T (z' - w) := hT.contDiffAt
    have hTcomp := (hTloc.differentiableAt one_ne_zero).hasFDerivAt.comp z' hinput
    have hcomp := (heatVecKernelCLM θ w).hasFDerivAt.comp z' hTcomp
    convert hcomp using 1 <;> rfl
  have hparam := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (s := Metric.ball z 1) (x₀ := z) (μ := (volume : Measure Plane))
    (F := F) (F' := F') (bound := fun w => heatKernel2 θ w * M₁)
    (Metric.ball_mem_nhds z one_pos) hFmeas hFint hFprimeMeas hbound hboundInt hdiff
  have hfun : (fun z' : Plane => heatVecConvolution θ T z') =
      fun z' => ∫ w : Plane, F z' w := by
    funext z'
    rfl
  exact hparam.congr_of_eventuallyEq (Eventually.of_forall (congrFun hfun))

/-- On smooth inputs, the classical directional derivative of the actual vector heat equals the
actual Gaussian convolution of the input derivative. -/
theorem fderiv_heatVecConvolution_apply {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    {T : Plane → Vec} (hT : UnforcedLeray.Sob.IsCylSmooth c T)
    (z e : Plane) :
    fderiv ℝ (heatVecConvolution θ T) z e =
      heatVecConvolution θ (fun x => fderiv ℝ T x e) z := by
  obtain ⟨M₀, _, hTbound⟩ :=
    UnforcedLeray.HeatCylinder.exists_global_bound_of_cylSmooth hc hT
  obtain ⟨M₁, _, hderivBound⟩ :=
    UnforcedLeray.HeatCylinder.exists_global_deriv_bound_of_cylSmooth hc hT
  have hfd := hasFDerivAt_heatVecConvolution hθ (hT.smooth.of_le (by norm_num))
    hTbound hderivBound z
  let J : Plane → Plane →L[ℝ] Vec := fun w =>
    (heatVecKernelCLM θ w).comp (fderiv ℝ T (z - w))
  have hkernel : Integrable (heatKernel2 θ) := UnforcedLeray.B0284.integrable_heatKernel2 hθ
  have hJmeas : AEStronglyMeasurable J volume := by
    have hder : Continuous (fun w : Plane => fderiv ℝ T (z - w)) :=
      (hT.smooth.continuous_fderiv (by norm_num)).comp
        (continuous_const.sub continuous_id)
    have hker := continuous_heatVecKernelCLM hθ
    exact (hker.clm_comp hder).measurable.aestronglyMeasurable
  have hJbound : ∀ᵐ w ∂(volume : Measure Plane),
      ‖J w‖ ≤ heatKernel2 θ w * M₁ := by
    filter_upwards [] with w
    calc
      ‖(heatVecKernelCLM θ w).comp (fderiv ℝ T (z - w))‖ ≤
          ‖heatVecKernelCLM θ w‖ * ‖fderiv ℝ T (z - w)‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ heatKernel2 θ w * M₁ := by
        exact mul_le_mul (norm_heatVecKernelCLM_le hθ w) (hderivBound (z - w))
          (norm_nonneg _) (UnforcedLeray.B0284.heatKernel2_nonneg hθ w)
  have hJint : Integrable J volume :=
    (hkernel.mul_const M₁).mono' hJmeas hJbound
  have hEval :
      (∫ w : Plane, (heatVecKernelCLM θ w).comp (fderiv ℝ T (z - w))) e =
        ∫ w : Plane, heatKernel2 θ w • fderiv ℝ T (z - w) e := by
    calc
      (∫ w : Plane, (heatVecKernelCLM θ w).comp (fderiv ℝ T (z - w))) e =
          ∫ w : Plane, ((heatVecKernelCLM θ w).comp (fderiv ℝ T (z - w))) e :=
        ContinuousLinearMap.integral_apply hJint e
      _ = ∫ w : Plane, heatKernel2 θ w • fderiv ℝ T (z - w) e := by
        congr 1
  rw [hfd.fderiv, hEval]
  rfl

end UnforcedLeray.HeatCylinder

#print axioms UnforcedLeray.HeatCylinder.hasFDerivAt_heatVecConvolution
#print axioms UnforcedLeray.HeatCylinder.fderiv_heatVecConvolution_apply
