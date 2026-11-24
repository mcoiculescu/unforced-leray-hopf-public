import UnforcedLeray.Lib.HeatCylinder.Derivative
import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.KernelDivergenceConvolution

/-!
# Absolute integrability for the actual two-stage Gaussian response

For bounded continuous periodic tensors, the literal scalar-heat / B0296-divergence double
integrand is Bochner integrable. This is the concrete Fubini input for the positive-age response
covariance; it does not itself assert that covariance.
-/

set_option autoImplicit false
set_option maxHeartbeats 500000

noncomputable section

open MeasureTheory
open scoped ENNReal
open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.B0284
open UnforcedLeray.B0296
open UnforcedLeray.HeatCylinder

namespace UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

private theorem integrable_gradKernelAbs_toReal {θ : ℝ} (hθ : 0 < θ) :
    Integrable (fun w : Plane => (gradKernelAbs θ w).toReal) := by
  have hkmeas : Measurable (fun w : Plane => gradKernelAbs θ w) := measurable_gradKernelAbs θ
  have hkfin : ∀ w : Plane, gradKernelAbs θ w ≠ ∞ := gradKernelAbs_ne_top θ
  refine ⟨hkmeas.ennreal_toReal.aestronglyMeasurable, ?_⟩
  change ∫⁻ w : Plane, ‖(gradKernelAbs θ w).toReal‖ₑ < ∞
  have hnorm : (fun w : Plane => ‖(gradKernelAbs θ w).toReal‖ₑ) = gradKernelAbs θ := by
    funext w
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (ENNReal.toReal_nonneg),
      ENNReal.ofReal_toReal (hkfin w)]
  rw [hnorm, lintegral_gradKernelAbs hθ]
  exact ENNReal.ofReal_lt_top

/-- Product-kernel integrability against a globally bounded continuous tensor, for the actual
B0284 heat kernel and B0296 divergence kernel. -/
theorem integrable_heatDiv_doubleIntegrand {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    {T : Plane → Plane × Plane} (hT : Continuous T) {M : ℝ}
    (hTb : ∀ z, ‖T z‖ ≤ M) (z : Plane) :
    Integrable (fun p : Plane × Plane =>
      heatKernel2 α p.1 • divKernelCLM β p.2 (T (z - p.1 - p.2)))
      ((volume : Measure Plane).prod volume) := by
  let G : Plane → ℝ := heatKernel2 α
  let K : Plane → ℝ := fun w => (gradKernelAbs β w).toReal
  let F : Plane × Plane → Plane := fun p => G p.1 •
    divKernelCLM β p.2 (T (z - p.1 - p.2))
  have hG : Integrable G := integrable_heatKernel2 hα
  have hK : Integrable K := integrable_gradKernelAbs_toReal hβ
  have hMajor : Integrable (fun p : Plane × Plane => M * (G p.1 * K p.2)) :=
    (hG.mul_prod hK).const_mul M
  have hFcont : Continuous F := by
    have hg : Continuous (fun w : Plane => divKernelCLM β w) := by
      unfold divKernelCLM
      have hq : Continuous (fun w : Plane => (gradHeatKernel2 β w).1) := by
        unfold gradHeatKernel2
        exact (continuous_dHeatKernel β).comp continuous_fst |>.mul
          ((continuous_heatKernel1 β).comp continuous_snd)
      have he : Continuous (fun w : Plane => (gradHeatKernel2 β w).2) := by
        unfold gradHeatKernel2
        exact ((continuous_heatKernel1 β).comp continuous_fst).mul
          ((continuous_dHeatKernel β).comp continuous_snd)
      exact (hq.smul continuous_const).add (he.smul continuous_const)
    have hGcont : Continuous G := by
      change Continuous (fun w : Plane => B0191.heatKernel 1 α w.1 *
        B0191.heatKernel 1 α w.2)
      exact ((continuous_heatKernel1 α).comp continuous_fst).mul
        ((continuous_heatKernel1 α).comp continuous_snd)
    change Continuous (fun p : Plane × Plane =>
      G p.1 • divKernelCLM β p.2 (T (z - p.1 - p.2)))
    have hEval : Continuous (fun p : Plane × Plane =>
        divKernelCLM β p.2 (T (z - p.1 - p.2))) := by fun_prop
    exact (hGcont.comp continuous_fst).smul hEval
  have hbound : ∀ p, ‖F p‖ ≤ M * (G p.1 * K p.2) := by
    intro p
    have hgauss : 0 ≤ G p.1 := heatKernel2_nonneg hα p.1
    have hgrad : ‖divKernelCLM β p.2 (T (z - p.1 - p.2))‖ ≤
        K p.2 * ‖T (z - p.1 - p.2)‖ := by
      calc
        _ ≤ ‖divKernelCLM β p.2‖ * ‖T (z - p.1 - p.2)‖ :=
          (divKernelCLM β p.2).le_opNorm _
        _ ≤ K p.2 * ‖T (z - p.1 - p.2)‖ :=
          mul_le_mul_of_nonneg_right (divKernelCLM_norm_le β p.2) (norm_nonneg _)
    calc
      ‖F p‖ = |G p.1| *
          ‖divKernelCLM β p.2 (T (z - p.1 - p.2))‖ := norm_smul _ _
      _ = G p.1 * ‖divKernelCLM β p.2 (T (z - p.1 - p.2))‖ := by
        rw [abs_of_nonneg hgauss]
      _ ≤ G p.1 * (K p.2 * ‖T (z - p.1 - p.2)‖) :=
        mul_le_mul_of_nonneg_left hgrad hgauss
      _ ≤ G p.1 * (K p.2 * M) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hTb _) (ENNReal.toReal_nonneg)) hgauss
      _ = M * (G p.1 * K p.2) := by ring
  have hF : Integrable F := hMajor.mono' hFcont.aestronglyMeasurable
    (Filter.Eventually.of_forall hbound)
  have hF' : Integrable F ((volume : Measure Plane).prod volume) := by
    rw [Measure.volume_eq_prod] at hF
    exact hF
  simpa [F, G, K] using hF'

end UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

#print axioms UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.integrable_heatDiv_doubleIntegrand
