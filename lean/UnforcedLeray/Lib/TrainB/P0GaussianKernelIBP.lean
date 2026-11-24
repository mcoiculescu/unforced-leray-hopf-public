import UnforcedLeray.Units.B0296.Conv
import UnforcedLeray.Units.B0284.Contraction
import UnforcedLeray.Units.B0151.DivCurl
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Gaussian integration by parts for the actual B0296 kernel

This is the scalar pointwise kernel identity needed to identify the actual heat-divergence
convolution with heat applied to a classical divergence on a smooth input.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open UnforcedLeray.GaussianVortex (Plane)
open scoped ContDiff

namespace UnforcedLeray.TrainB

/-- Transfer one derivative from the actual planar Gaussian kernel to a smooth field evaluated at
`z - w`. The proof is the whole-plane integration-by-parts theorem with integrability supplied
by the actual Gaussian and its first derivatives. -/
theorem integral_heatKernel2_fderiv_mul_comp_sub {θ : ℝ} (hθ : 0 < θ)
    {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfBound : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖f x‖ ≤ M)
    (hfDerivBound : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖fderiv ℝ f x‖ ≤ M)
    (z e : Plane) :
    ∫ w : Plane,
        fderiv ℝ (UnforcedLeray.B0284.heatKernel2 θ) w e * f (z - w) =
      ∫ w : Plane,
        UnforcedLeray.B0284.heatKernel2 θ w * fderiv ℝ f (z - w) e := by
  let K : Plane → ℝ := UnforcedLeray.B0284.heatKernel2 θ
  let G : Plane → ℝ := fun w => f (z - w)
  obtain ⟨M, hM, hfb⟩ := hfBound
  obtain ⟨N, hN, hdfb⟩ := hfDerivBound
  have hK : Integrable K := by
    exact UnforcedLeray.B0284.integrable_heatKernel2 hθ
  have hKq : Integrable (fun w : Plane =>
      UnforcedLeray.B0296.dHeatKernel θ w.1 *
        UnforcedLeray.B0191.heatKernel 1 θ w.2) := by
    exact (UnforcedLeray.B0296.integrable_dHeatKernel hθ).mul_prod
      (UnforcedLeray.B0296.integrable_heatKernel1 hθ)
  have hKeta : Integrable (fun w : Plane =>
      UnforcedLeray.B0191.heatKernel 1 θ w.1 *
        UnforcedLeray.B0296.dHeatKernel θ w.2) := by
    exact (UnforcedLeray.B0296.integrable_heatKernel1 hθ).mul_prod
      (UnforcedLeray.B0296.integrable_dHeatKernel hθ)
  have hKdiff : Differentiable ℝ K := by
    change Differentiable ℝ (fun w : Plane =>
      UnforcedLeray.B0191.heatKernel 1 θ w.1 *
        UnforcedLeray.B0191.heatKernel 1 θ w.2)
    have hq : ContDiff ℝ ⊤ (fun w : Plane =>
        UnforcedLeray.B0191.heatKernel 1 θ w.1) :=
      (UnforcedLeray.B0191.contDiff_heatKernel 1 θ).comp contDiff_fst
    have hη : ContDiff ℝ ⊤ (fun w : Plane =>
        UnforcedLeray.B0191.heatKernel 1 θ w.2) :=
      (UnforcedLeray.B0191.contDiff_heatKernel 1 θ).comp contDiff_snd
    exact hq.differentiable (by simp) |>.mul (hη.differentiable (by simp))
  have hKq' (w : Plane) : fderiv ℝ K w (1, 0) =
      (UnforcedLeray.B0296.gradHeatKernel2 θ w).1 := by
    have hp := UnforcedLeray.B0151.partialX_eq_fderiv hKdiff w
    rw [← hp]
    have hd := (UnforcedLeray.B0296.hasDerivAt_heatKernel2_fst hθ.ne' w).deriv
    simpa [K, UnforcedLeray.B0284.heatKernel2,
      UnforcedLeray.GaussianVortex.partialX] using hd
  have hKeta' (w : Plane) : fderiv ℝ K w (0, 1) =
      (UnforcedLeray.B0296.gradHeatKernel2 θ w).2 := by
    have hp := UnforcedLeray.B0151.partialY_eq_fderiv hKdiff w
    rw [← hp]
    have hd := (UnforcedLeray.B0296.hasDerivAt_heatKernel2_snd hθ.ne' w).deriv
    simpa [K, UnforcedLeray.B0284.heatKernel2,
      UnforcedLeray.GaussianVortex.partialY] using hd
  have hKdiffInt : Integrable (fun w => fderiv ℝ K w e) := by
    have hq : Integrable (fun w : Plane => fderiv ℝ K w (1, 0)) := by
      refine hKq.congr (Filter.Eventually.of_forall fun w => ?_)
      simpa [UnforcedLeray.B0296.gradHeatKernel2] using (hKq' w).symm
    have heta : Integrable (fun w : Plane => fderiv ℝ K w (0, 1)) := by
      refine hKeta.congr (Filter.Eventually.of_forall fun w => ?_)
      simpa [UnforcedLeray.B0296.gradHeatKernel2] using (hKeta' w).symm
    have he : e = e.1 • ((1 : ℝ), (0 : ℝ)) + e.2 • ((0 : ℝ), (1 : ℝ)) := by
      ext <;> simp
    have hpoint (w : Plane) : fderiv ℝ K w e =
        e.1 * fderiv ℝ K w (1, 0) + e.2 * fderiv ℝ K w (0, 1) := by
      rw [he, map_add, map_smul, map_smul]
      simp [smul_eq_mul]
    have hEq : (fun w => fderiv ℝ K w e) = fun w =>
        e.1 * fderiv ℝ K w (1, 0) + e.2 * fderiv ℝ K w (0, 1) := funext hpoint
    rw [hEq]
    exact (hq.const_mul _).add (heta.const_mul _)
  have hGcont : Continuous G := by
    dsimp [G]
    exact hf.continuous.comp (continuous_const.sub continuous_id)
  have hGbound : ∀ w, ‖G w‖ ≤ M := fun w => hfb (z - w)
  have hGdiff : Differentiable ℝ G := by
    dsimp [G]
    have hmap : ContDiff ℝ ∞ (fun w : Plane => z - w) := by
      exact contDiff_const.sub contDiff_id
    exact (hf.comp hmap).differentiable (by simp)
  have hGderiv (w : Plane) : fderiv ℝ G w e =
      -(fderiv ℝ f (z - w) e) := by
    dsimp [G]
    have hmap : HasFDerivAt (fun y : Plane => z - y)
        (-ContinuousLinearMap.id ℝ Plane) w := (hasFDerivAt_id w).const_sub z
    have hcomp := (hf.differentiable (by simp) (z - w)).hasFDerivAt.comp w hmap
    change fderiv ℝ (f ∘ (fun y : Plane => z - y)) w e = _
    rw [hcomp.fderiv]
    simp
  have hGderivBound : ∀ w, ‖fderiv ℝ G w e‖ ≤ N * ‖e‖ := by
    intro w
    rw [hGderiv w, norm_neg]
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (hdfb (z - w)) (norm_nonneg _))
  have hGderivCont : Continuous (fun w => fderiv ℝ G w e) := by
    have hsmooth : ContDiff ℝ 1 G := by
      dsimp [G]
      have hmap : ContDiff ℝ 1 (fun w : Plane => z - w) := by
        exact contDiff_const.sub contDiff_id
      exact hf.of_le (by norm_num) |>.comp hmap
    exact (hsmooth.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hI1' : Integrable (fun w => G w * fderiv ℝ K w e) := by
    exact hKdiffInt.bdd_mul hGcont.aestronglyMeasurable (c := M)
      (Filter.Eventually.of_forall hGbound)
  have hI1 : Integrable (fun w => fderiv ℝ K w e * G w) :=
    hI1'.congr (Filter.Eventually.of_forall fun w => mul_comm (G w) _)
  have hI2' : Integrable (fun w => fderiv ℝ G w e * K w) := by
    exact hK.bdd_mul hGderivCont.aestronglyMeasurable (c := N * ‖e‖)
      (Filter.Eventually.of_forall hGderivBound)
  have hI2 : Integrable (fun w => K w * fderiv ℝ G w e) :=
    hI2'.congr (Filter.Eventually.of_forall fun w => mul_comm _ _)
  have hI3' : Integrable (fun w => G w * K w) := by
    exact hK.bdd_mul hGcont.aestronglyMeasurable (c := M)
      (Filter.Eventually.of_forall hGbound)
  have hI3 : Integrable (fun w => K w * G w) :=
    hI3'.congr (Filter.Eventually.of_forall fun w => mul_comm _ _)
  have hIBP := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    hI1 hI2 hI3 (fun w _ => hKdiff w) (fun w _ => hGdiff w)
  have hIBP' : ∫ w, K w * fderiv ℝ G w e = -∫ w, fderiv ℝ K w e * G w := hIBP
  rw [show (fun w : Plane => fderiv ℝ K w e * f (z - w)) =
      fun w => fderiv ℝ K w e * G w from rfl,
    show (fun w : Plane => K w * fderiv ℝ f (z - w) e) =
      fun w => -(K w * fderiv ℝ G w e) from funext fun w => by
        rw [hGderiv w]
        ring]
  rw [integral_neg, hIBP']
  ring

#print axioms UnforcedLeray.TrainB.integral_heatKernel2_fderiv_mul_comp_sub

end UnforcedLeray.TrainB
