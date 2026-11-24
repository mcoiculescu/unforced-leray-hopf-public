import UnforcedLeray.Lib.TrainB.P0GaussianKernelIBP

/-!
# Row-divergence Gaussian integration by parts

The scalar identity is applied to each physical vector coordinate. This leaf keeps the
row-oriented B0296 tensor convention explicit.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open UnforcedLeray.GaussianVortex (Plane)
open scoped ContDiff

namespace UnforcedLeray.TrainB

/-- Classical row divergence of a tensor `T = (T_q,T_η)`, componentwise. -/
def classicalRowDiv (T : Plane → Plane × Plane) (z : Plane) : Plane :=
  (fderiv ℝ (fun x => (T x).1.1) z (1, 0) +
      fderiv ℝ (fun x => (T x).2.1) z (0, 1),
    fderiv ℝ (fun x => (T x).1.2) z (1, 0) +
      fderiv ℝ (fun x => (T x).2.2) z (0, 1))

private theorem integrable_kernel_times_comp_sub {θ : ℝ} (hθ : 0 < θ)
    {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfb : ∃ M : ℝ, ∀ x, ‖f x‖ ≤ M) (z : Plane) :
    Integrable (fun w : Plane => UnforcedLeray.B0284.heatKernel2 θ w * f (z - w)) := by
  obtain ⟨M, hM⟩ := hfb
  have hK := UnforcedLeray.B0284.integrable_heatKernel2 hθ
  have hGcont : Continuous (fun w : Plane => f (z - w)) :=
    hf.continuous.comp (continuous_const.sub continuous_id)
  have hGbound : ∀ w, ‖f (z - w)‖ ≤ M := fun w => hM (z - w)
  have hi := hK.bdd_mul hGcont.aestronglyMeasurable (c := M)
    (Filter.Eventually.of_forall hGbound)
  exact hi.congr (Filter.Eventually.of_forall fun w => mul_comm _ _)

private theorem integrable_qKernel_times_comp_sub {θ : ℝ} (hθ : 0 < θ)
    {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfb : ∃ M : ℝ, ∀ x, ‖f x‖ ≤ M) (z : Plane) :
    Integrable (fun w : Plane =>
      (UnforcedLeray.B0296.gradHeatKernel2 θ w).1 * f (z - w)) := by
  obtain ⟨M, hM⟩ := hfb
  have hGcont : Continuous (fun w : Plane => f (z - w)) :=
    hf.continuous.comp (continuous_const.sub continuous_id)
  have hGbound : ∀ w, ‖f (z - w)‖ ≤ M := fun w => hM (z - w)
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
  have hi0 := hKq.bdd_mul hGcont.aestronglyMeasurable (c := M)
    (Filter.Eventually.of_forall hGbound)
  refine hi0.congr (Filter.Eventually.of_forall fun w => ?_)
  simp [UnforcedLeray.B0296.gradHeatKernel2]
  ring

private theorem integrable_etaKernel_times_comp_sub {θ : ℝ} (hθ : 0 < θ)
    {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfb : ∃ M : ℝ, ∀ x, ‖f x‖ ≤ M) (z : Plane) :
    Integrable (fun w : Plane =>
      (UnforcedLeray.B0296.gradHeatKernel2 θ w).2 * f (z - w)) := by
  obtain ⟨M, hM⟩ := hfb
  have hGcont : Continuous (fun w : Plane => f (z - w)) :=
    hf.continuous.comp (continuous_const.sub continuous_id)
  have hGbound : ∀ w, ‖f (z - w)‖ ≤ M := fun w => hM (z - w)
  have hKeta : Integrable (fun w : Plane =>
      UnforcedLeray.B0191.heatKernel 1 θ w.1 *
        UnforcedLeray.B0296.dHeatKernel θ w.2) := by
    exact (UnforcedLeray.B0296.integrable_heatKernel1 hθ).mul_prod
      (UnforcedLeray.B0296.integrable_dHeatKernel hθ)
  have hi := hKeta.bdd_mul hGcont.aestronglyMeasurable (c := M)
    (Filter.Eventually.of_forall hGbound)
  refine hi.congr (Filter.Eventually.of_forall fun w => ?_)
  simp [UnforcedLeray.B0296.gradHeatKernel2]
  ring

private theorem integrable_kernel_times_deriv_comp_sub {θ : ℝ} (hθ : 0 < θ)
    {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f)
    (hdfb : ∃ M : ℝ, ∀ x, ‖fderiv ℝ f x‖ ≤ M) (z e : Plane) :
    Integrable (fun w : Plane => UnforcedLeray.B0284.heatKernel2 θ w *
      fderiv ℝ f (z - w) e) := by
  obtain ⟨M, hM⟩ := hdfb
  have hK := UnforcedLeray.B0284.integrable_heatKernel2 hθ
  have hmap : ContDiff ℝ 1 (fun w : Plane => z - w) := by
    exact contDiff_const.sub contDiff_id
  have hsmooth : ContDiff ℝ 1 (fun w : Plane => f (z - w)) :=
    hf.of_le (by norm_num) |>.comp hmap
  have hGcont : Continuous (fun w : Plane => fderiv ℝ (fun y : Plane => f (z - y)) w e) :=
    (hsmooth.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hGbound : ∀ w, ‖fderiv ℝ f (z - w) e‖ ≤ M * ‖e‖ := by
    intro w
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (hM (z - w)) (norm_nonneg _))
  have hGderiv (w : Plane) :
      fderiv ℝ (fun y : Plane => f (z - y)) w e =
        -(fderiv ℝ f (z - w) e) := by
    have hmap' : HasFDerivAt (fun y : Plane => z - y)
        (-ContinuousLinearMap.id ℝ Plane) w := (hasFDerivAt_id w).const_sub z
    have hcomp := (hf.differentiable (by simp) (z - w)).hasFDerivAt.comp w hmap'
    have hcomp' := hcomp.fderiv
    change fderiv ℝ (fun y : Plane => f (z - y)) w = _ at hcomp'
    rw [hcomp']
    simp
  have hGbound' : ∀ w,
      ‖fderiv ℝ (fun y : Plane => f (z - y)) w e‖ ≤ M * ‖e‖ := by
    intro w
    rw [hGderiv, norm_neg]
    exact hGbound w
  have hi := hK.bdd_mul hGcont.aestronglyMeasurable (c := M * ‖e‖)
    (Filter.Eventually.of_forall hGbound')
  refine hi.neg.congr (Filter.Eventually.of_forall fun w => ?_)
  change -((fderiv ℝ (fun y : Plane => f (z - y)) w e) *
      UnforcedLeray.B0284.heatKernel2 θ w) = _
  rw [hGderiv w]
  ring

/-- The actual two-coordinate Gaussian transfers the row divergence to the field, with the
positive sign dictated by the two integrations by parts. -/
theorem integral_gradKernel_row_eq_integral_kernel_rowDiv {θ : ℝ} (hθ : 0 < θ)
    {f g : Plane → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hfBound : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖f x‖ ≤ M)
    (hgBound : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖g x‖ ≤ M)
    (hfDerivBound : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖fderiv ℝ f x‖ ≤ M)
    (hgDerivBound : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖fderiv ℝ g x‖ ≤ M)
    (z : Plane) :
    ∫ w : Plane,
        (UnforcedLeray.B0296.gradHeatKernel2 θ w).1 * f (z - w) +
          (UnforcedLeray.B0296.gradHeatKernel2 θ w).2 * g (z - w) =
      ∫ w : Plane, UnforcedLeray.B0284.heatKernel2 θ w *
        (fderiv ℝ f (z - w) (1, 0) + fderiv ℝ g (z - w) (0, 1)) := by
  have hfB' : ∃ M : ℝ, ∀ x, ‖f x‖ ≤ M := ⟨hfBound.choose, hfBound.choose_spec.2⟩
  have hgB' : ∃ M : ℝ, ∀ x, ‖g x‖ ≤ M := ⟨hgBound.choose, hgBound.choose_spec.2⟩
  have hqf := integrable_qKernel_times_comp_sub hθ hf hfB' z
  have hetag := integrable_etaKernel_times_comp_sub hθ hg hgB' z
  have hdf := integrable_kernel_times_deriv_comp_sub hθ hf
    ⟨hfDerivBound.choose, hfDerivBound.choose_spec.2⟩ z (1, 0)
  have hdg := integrable_kernel_times_deriv_comp_sub hθ hg
    ⟨hgDerivBound.choose, hgDerivBound.choose_spec.2⟩ z (0, 1)
  have hq := integral_heatKernel2_fderiv_mul_comp_sub hθ hf hfBound
    hfDerivBound z (1, 0)
  have heta := integral_heatKernel2_fderiv_mul_comp_sub hθ hg hgBound
    hgDerivBound z (0, 1)
  have hKdiff : Differentiable ℝ (UnforcedLeray.B0284.heatKernel2 θ) := by
    change Differentiable ℝ (fun w : Plane =>
      UnforcedLeray.B0191.heatKernel 1 θ w.1 *
        UnforcedLeray.B0191.heatKernel 1 θ w.2)
    have hq' : ContDiff ℝ ⊤ (fun w : Plane =>
        UnforcedLeray.B0191.heatKernel 1 θ w.1) :=
      (UnforcedLeray.B0191.contDiff_heatKernel 1 θ).comp contDiff_fst
    have heta' : ContDiff ℝ ⊤ (fun w : Plane =>
        UnforcedLeray.B0191.heatKernel 1 θ w.2) :=
      (UnforcedLeray.B0191.contDiff_heatKernel 1 θ).comp contDiff_snd
    exact hq'.differentiable (by simp) |>.mul (heta'.differentiable (by simp))
  have hGradQ (w : Plane) :
      (UnforcedLeray.B0296.gradHeatKernel2 θ w).1 =
        fderiv ℝ (UnforcedLeray.B0284.heatKernel2 θ) w (1, 0) := by
    have hp := UnforcedLeray.B0151.partialX_eq_fderiv hKdiff w
    have hd := (UnforcedLeray.B0296.hasDerivAt_heatKernel2_fst hθ.ne' w).deriv
    rw [← hp]
    simpa [UnforcedLeray.B0284.heatKernel2,
      UnforcedLeray.GaussianVortex.partialX] using hd.symm
  have hGradEta (w : Plane) :
      (UnforcedLeray.B0296.gradHeatKernel2 θ w).2 =
        fderiv ℝ (UnforcedLeray.B0284.heatKernel2 θ) w (0, 1) := by
    have hp := UnforcedLeray.B0151.partialY_eq_fderiv hKdiff w
    have hd := (UnforcedLeray.B0296.hasDerivAt_heatKernel2_snd hθ.ne' w).deriv
    rw [← hp]
    simpa [UnforcedLeray.B0284.heatKernel2,
      UnforcedLeray.GaussianVortex.partialY] using hd.symm
  calc
    _ = (∫ w : Plane,
          (UnforcedLeray.B0296.gradHeatKernel2 θ w).1 * f (z - w)) +
        (∫ w : Plane,
          (UnforcedLeray.B0296.gradHeatKernel2 θ w).2 * g (z - w)) :=
      integral_add hqf hetag
    _ = (∫ w : Plane, fderiv ℝ (UnforcedLeray.B0284.heatKernel2 θ) w (1, 0) *
          f (z - w)) +
        (∫ w : Plane, fderiv ℝ (UnforcedLeray.B0284.heatKernel2 θ) w (0, 1) *
          g (z - w)) := by
      congr 1
      · apply integral_congr_ae
        filter_upwards with w
        rw [hGradQ w]
      · apply integral_congr_ae
        filter_upwards with w
        rw [hGradEta w]
    _ = (∫ w : Plane, UnforcedLeray.B0284.heatKernel2 θ w *
          fderiv ℝ f (z - w) (1, 0)) +
        (∫ w : Plane, UnforcedLeray.B0284.heatKernel2 θ w *
          fderiv ℝ g (z - w) (0, 1)) := by rw [hq, heta]
    _ = ∫ w : Plane, UnforcedLeray.B0284.heatKernel2 θ w *
          (fderiv ℝ f (z - w) (1, 0) + fderiv ℝ g (z - w) (0, 1)) := by
      rw [← integral_add hdf hdg]
      congr 1
      funext w
      ring

end UnforcedLeray.TrainB

#print axioms UnforcedLeray.TrainB.integral_gradKernel_row_eq_integral_kernel_rowDiv
