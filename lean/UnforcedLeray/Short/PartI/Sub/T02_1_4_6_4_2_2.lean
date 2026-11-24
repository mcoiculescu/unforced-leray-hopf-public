import UnforcedLeray.Short.PartI.Sub.T02_1_4_6_4_2
import UnforcedLeray.Lib.TrainB.P0GaussianHeatKernelEquation
import UnforcedLeray.Lib.HeatCylinder.HeatKernelAgeIntegrable
import UnforcedLeray.Units.B0151.DivCurl

/-!
# Part I, leaf `PartI:T02/1/4/6/4/2/2` (`LeafAgeIBPCH`)

Smooth (`C^infinity`) version of the Gaussian age integration by parts. The bodies of
`Lib/TrainB/P0GaussianKernelIBP.lean` and `Lib/TrainB/P0GaussianSecondOrderIBP.lean` are copied
into the namespace `UnforcedLeray.Short.PartI.IBPLeaf` with `ContDiff ℝ ⊤` replaced by
`ContDiff ℝ ∞` (the originals assume analyticity). The copy is otherwise unchanged. The leaf
then follows from the base point `z = 0` and the evenness of the Gaussian and its age derivative,
via `integral_neg_eq_self`.
-/

set_option autoImplicit false

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

namespace UnforcedLeray.Short.PartI.IBPLeaf

/-- Transfer one derivative from the actual planar Gaussian kernel to a smooth field evaluated at
`z - w`. The proof is the whole-plane integration-by-parts theorem with integrability supplied
by the actual Gaussian and its first derivatives. -/
private theorem hkCD (θ : ℝ) :
    ContDiff ℝ ∞ (UnforcedLeray.B0191.heatKernel 1 θ) :=
  (UnforcedLeray.B0191.contDiff_heatKernel 1 θ).of_le le_top

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
    have hq : ContDiff ℝ ∞ (fun w : Plane =>
        UnforcedLeray.B0191.heatKernel 1 θ w.1) :=
      (hkCD θ).comp contDiff_fst
    have hη : ContDiff ℝ ∞ (fun w : Plane =>
        UnforcedLeray.B0191.heatKernel 1 θ w.2) :=
      (hkCD θ).comp contDiff_snd
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


end UnforcedLeray.Short.PartI.IBPLeaf

/-! Whole-plane second-order integration by parts for the actual planar Gaussian. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace UnforcedLeray.Short.PartI.IBPLeaf
open UnforcedLeray.GaussianVortex (Plane partialX partialY)
open scoped ContDiff

private theorem integral_comp_sub_second_ibp {K₁ K₂ f h : Plane → ℝ}
    (e z : Plane) (hK₁Diff : Differentiable ℝ K₁)
    (hK₁Int : Integrable K₁) (hK₂Int : Integrable K₂)
    (hK₂ : ∀ w, fderiv ℝ K₁ w e = K₂ w)
    (hf : ContDiff ℝ ∞ f) (hfBound : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖f x‖ ≤ M)
    (hh : ContDiff ℝ ∞ h) (hhBound : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖h x‖ ≤ M)
    (hGderiv : ∀ w, fderiv ℝ (fun y => f (z - y)) w e = -h (z - w)) :
    ∫ w : Plane, K₂ w * f (z - w) = ∫ w, K₁ w * h (z - w) := by
  let G : Plane → ℝ := fun w => f (z - w)
  have hGcont : Continuous G := hf.continuous.comp (continuous_const.sub continuous_id)
  have hGdiff : Differentiable ℝ G := (hf.comp (contDiff_const.sub contDiff_id)).differentiable (by simp)
  have hGderivCont : Continuous (fun w => fderiv ℝ G w e) := by
    have hGcd : ContDiff ℝ 1 G := (hf.comp (contDiff_const.sub contDiff_id)).of_le (by norm_num)
    exact (hGcd.continuous_fderiv (by norm_num)).clm_apply continuous_const
  obtain ⟨M, hM, hMf⟩ := hfBound
  obtain ⟨N, hN, hMh⟩ := hhBound
  have hGbound : ∀ w, ‖G w‖ ≤ M := fun w => hMf (z - w)
  have hGderivBound : ∀ w, ‖fderiv ℝ G w e‖ ≤ N := by
    intro w
    rw [hGderiv w, norm_neg]
    exact hMh (z - w)
  have hKderivInt : Integrable (fun w => fderiv ℝ K₁ w e) := by
    refine hK₂Int.congr (Filter.Eventually.of_forall fun w => ?_)
    exact (hK₂ w).symm
  have hI₁' : Integrable (fun w => G w * fderiv ℝ K₁ w e) :=
    hKderivInt.bdd_mul hGcont.aestronglyMeasurable (c := M)
      (Filter.Eventually.of_forall hGbound)
  have hI₁ : Integrable (fun w => fderiv ℝ K₁ w e * G w) :=
    hI₁'.congr (Filter.Eventually.of_forall fun w => mul_comm _ _)
  have hI₂' : Integrable (fun w => fderiv ℝ G w e * K₁ w) :=
    hK₁Int.bdd_mul hGderivCont.aestronglyMeasurable (c := N)
      (Filter.Eventually.of_forall hGderivBound)
  have hI₂ : Integrable (fun w => K₁ w * fderiv ℝ G w e) :=
    hI₂'.congr (Filter.Eventually.of_forall fun w => mul_comm _ _)
  have hI₃' : Integrable (fun w => G w * K₁ w) :=
    hK₁Int.bdd_mul hGcont.aestronglyMeasurable (c := M)
      (Filter.Eventually.of_forall hGbound)
  have hI₃ : Integrable (fun w => K₁ w * G w) :=
    hI₃'.congr (Filter.Eventually.of_forall fun w => mul_comm _ _)
  have hIBP := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    hI₁ hI₂ hI₃ (fun w _ => hK₁Diff w) (fun w _ => hGdiff w)
  have hA : ∫ w, K₂ w * G w = ∫ w, fderiv ℝ K₁ w e * G w := by
    apply integral_congr_ae
    filter_upwards with w
    rw [← hK₂ w]
  have hB : (∫ w, K₁ w * fderiv ℝ G w e) = -(∫ w, K₁ w * h (z - w)) := by
    calc
      _ = ∫ w, -(K₁ w * h (z - w)) := by
        apply integral_congr_ae
        filter_upwards with w
        rw [hGderiv w]
        ring
      _ = _ := integral_neg _
  calc
    ∫ w, K₂ w * f (z - w) = ∫ w, fderiv ℝ K₁ w e * G w := by simpa [G] using hA
    _ = -∫ w, K₁ w * fderiv ℝ G w e := by rw [hIBP]; ring
    _ = ∫ w, K₁ w * h (z - w) := by rw [hB]; ring

private theorem deriv_dHeatKernel_formula {θ x : ℝ} (hθ : θ ≠ 0) :
    deriv (UnforcedLeray.B0296.dHeatKernel θ) x =
      ((x ^ 2 / (4 * θ ^ 2)) - 1 / (2 * θ)) *
        UnforcedLeray.B0191.heatKernel 1 θ x := by
  have hcoef : (fun y : ℝ => -(y / (2 * θ))) = fun y => (-(1 / (2 * θ))) * y := by
    funext y
    ring
  unfold UnforcedLeray.B0296.dHeatKernel
  change deriv ((fun y : ℝ => -(y / (2 * θ))) *
    (UnforcedLeray.B0191.heatKernel 1 θ)) x = _
  have hcoefDiff : DifferentiableAt ℝ (fun y : ℝ => -(y / (2 * θ))) x := by fun_prop
  have hkernelDiff : DifferentiableAt ℝ (UnforcedLeray.B0191.heatKernel 1 θ) x :=
    ((UnforcedLeray.B0191.contDiff_heatKernel 1 θ).differentiable (by simp)).differentiableAt
  rw [deriv_mul hcoefDiff hkernelDiff, hcoef, deriv_const_mul_id]
  rw [(UnforcedLeray.B0296.hasDerivAt_heatKernel hθ x).deriv]
  rw [UnforcedLeray.B0296.dHeatKernel]
  field_simp [hθ]
  ring

private theorem qSecondKernel {θ : ℝ} (hθ : 0 < θ) (w : Plane) :
    partialX (fun y : Plane => (UnforcedLeray.B0296.gradHeatKernel2 θ y).1) w =
      ((w.1 ^ 2 / (4 * θ ^ 2) - 1 / (2 * θ)) *
        UnforcedLeray.B0191.heatKernel 1 θ w.1) *
          UnforcedLeray.B0191.heatKernel 1 θ w.2 := by
  rcases w with ⟨q, η⟩
  change deriv (fun x : ℝ => UnforcedLeray.B0296.dHeatKernel θ x *
    UnforcedLeray.B0191.heatKernel 1 θ η) q = _
  rw [deriv_mul_const_field, deriv_dHeatKernel_formula hθ.ne']

private theorem etaSecondKernel {θ : ℝ} (hθ : 0 < θ) (w : Plane) :
    partialY (fun y : Plane => (UnforcedLeray.B0296.gradHeatKernel2 θ y).2) w =
      UnforcedLeray.B0191.heatKernel 1 θ w.1 *
        ((w.2 ^ 2 / (4 * θ ^ 2) - 1 / (2 * θ)) *
          UnforcedLeray.B0191.heatKernel 1 θ w.2) := by
  rcases w with ⟨q, η⟩
  change deriv (fun y : ℝ => UnforcedLeray.B0191.heatKernel 1 θ q *
    UnforcedLeray.B0296.dHeatKernel θ y) η = _
  rw [deriv_const_mul_field, deriv_dHeatKernel_formula hθ.ne']

private theorem integrable_qSecondKernel {θ : ℝ} (hθ : 0 < θ) :
    Integrable (fun w : Plane =>
      ((w.1 ^ 2 / (4 * θ ^ 2) - 1 / (2 * θ)) *
        UnforcedLeray.B0191.heatKernel 1 θ w.1) *
          UnforcedLeray.B0191.heatKernel 1 θ w.2) := by
  have h0 : Integrable (UnforcedLeray.B0191.heatKernel 1 θ) :=
    UnforcedLeray.B0296.integrable_heatKernel1 hθ
  have h2 : Integrable (fun x : ℝ => x ^ 2 * UnforcedLeray.B0191.heatKernel 1 θ x) :=
    UnforcedLeray.HeatCylinder.integrable_sq_mul_heatKernel1 hθ
  have h20 := (h2.div_const (4 * θ ^ 2)).mul_prod h0
  have h00 := (h0.mul_prod h0).div_const (2 * θ)
  have hsum : Integrable (fun w : Plane =>
      ((w.1 ^ 2 * UnforcedLeray.B0191.heatKernel 1 θ w.1) / (4 * θ ^ 2)) *
        UnforcedLeray.B0191.heatKernel 1 θ w.2 -
      (UnforcedLeray.B0191.heatKernel 1 θ w.1 *
        UnforcedLeray.B0191.heatKernel 1 θ w.2) / (2 * θ)) := by
    exact h20.sub h00
  have heq : (fun w : Plane =>
      ((w.1 ^ 2 / (4 * θ ^ 2) - 1 / (2 * θ)) *
        UnforcedLeray.B0191.heatKernel 1 θ w.1) *
          UnforcedLeray.B0191.heatKernel 1 θ w.2) = fun w =>
      ((w.1 ^ 2 * UnforcedLeray.B0191.heatKernel 1 θ w.1) / (4 * θ ^ 2)) *
        UnforcedLeray.B0191.heatKernel 1 θ w.2 -
      (UnforcedLeray.B0191.heatKernel 1 θ w.1 *
        UnforcedLeray.B0191.heatKernel 1 θ w.2) / (2 * θ) := by
    funext w
    ring
  rw [heq, Measure.volume_eq_prod]
  exact hsum

private theorem integrable_etaSecondKernel {θ : ℝ} (hθ : 0 < θ) :
    Integrable (fun w : Plane =>
      (UnforcedLeray.B0191.heatKernel 1 θ w.1 *
        ((w.2 ^ 2 / (4 * θ ^ 2) - 1 / (2 * θ)) *
          UnforcedLeray.B0191.heatKernel 1 θ w.2))) := by
  have h0 : Integrable (UnforcedLeray.B0191.heatKernel 1 θ) :=
    UnforcedLeray.B0296.integrable_heatKernel1 hθ
  have h2 : Integrable (fun x : ℝ => x ^ 2 * UnforcedLeray.B0191.heatKernel 1 θ x) :=
    UnforcedLeray.HeatCylinder.integrable_sq_mul_heatKernel1 hθ
  have h02 := h0.mul_prod (h2.div_const (4 * θ ^ 2))
  have h00 := (h0.mul_prod h0).div_const (2 * θ)
  have hsum : Integrable (fun w : Plane =>
      UnforcedLeray.B0191.heatKernel 1 θ w.1 *
        ((w.2 ^ 2 * UnforcedLeray.B0191.heatKernel 1 θ w.2) / (4 * θ ^ 2)) -
      (UnforcedLeray.B0191.heatKernel 1 θ w.1 *
        UnforcedLeray.B0191.heatKernel 1 θ w.2) / (2 * θ)) := by
    exact h02.sub h00
  have heq : (fun w : Plane =>
      (UnforcedLeray.B0191.heatKernel 1 θ w.1 *
        ((w.2 ^ 2 / (4 * θ ^ 2) - 1 / (2 * θ)) *
          UnforcedLeray.B0191.heatKernel 1 θ w.2))) = fun w =>
      UnforcedLeray.B0191.heatKernel 1 θ w.1 *
        ((w.2 ^ 2 * UnforcedLeray.B0191.heatKernel 1 θ w.2) / (4 * θ ^ 2)) -
      (UnforcedLeray.B0191.heatKernel 1 θ w.1 *
        UnforcedLeray.B0191.heatKernel 1 θ w.2) / (2 * θ) := by
    funext w
    ring
  rw [heq, Measure.volume_eq_prod]
  exact hsum

private theorem hkDiff2 (θ : ℝ) : Differentiable ℝ (UnforcedLeray.B0284.heatKernel2 θ) := by
  change Differentiable ℝ (fun w : Plane =>
    UnforcedLeray.B0191.heatKernel 1 θ w.1 * UnforcedLeray.B0191.heatKernel 1 θ w.2)
  exact (((hkCD θ).comp contDiff_fst).mul ((hkCD θ).comp contDiff_snd)).differentiable (by simp)

private theorem dHeatKernel_diff (θ : ℝ) : Differentiable ℝ (UnforcedLeray.B0296.dHeatKernel θ) := by
  unfold UnforcedLeray.B0296.dHeatKernel
  exact ((differentiable_id.div_const _).neg).mul ((hkCD θ).differentiable (by simp))

private theorem gradFst_diff (θ : ℝ) :
    Differentiable ℝ (fun y : Plane => (UnforcedLeray.B0296.gradHeatKernel2 θ y).1) := by
  change Differentiable ℝ (fun y : Plane => UnforcedLeray.B0296.dHeatKernel θ y.1 *
    UnforcedLeray.B0191.heatKernel 1 θ y.2)
  exact ((dHeatKernel_diff θ).comp differentiable_fst).mul
    (((hkCD θ).differentiable (by simp)).comp differentiable_snd)

private theorem gradSnd_diff (θ : ℝ) :
    Differentiable ℝ (fun y : Plane => (UnforcedLeray.B0296.gradHeatKernel2 θ y).2) := by
  change Differentiable ℝ (fun y : Plane => UnforcedLeray.B0191.heatKernel 1 θ y.1 *
    UnforcedLeray.B0296.dHeatKernel θ y.2)
  exact (((hkCD θ).differentiable (by simp)).comp differentiable_fst).mul
    ((dHeatKernel_diff θ).comp differentiable_snd)

private theorem fderivK_fst {θ : ℝ} (hθ : 0 < θ) (w : Plane) :
    fderiv ℝ (UnforcedLeray.B0284.heatKernel2 θ) w (1, 0) =
      (UnforcedLeray.B0296.gradHeatKernel2 θ w).1 := by
  have hp := UnforcedLeray.B0151.partialX_eq_fderiv (hkDiff2 θ) w
  rw [← hp]
  have hd := (UnforcedLeray.B0296.hasDerivAt_heatKernel2_fst hθ.ne' w).deriv
  simpa [UnforcedLeray.B0284.heatKernel2, UnforcedLeray.GaussianVortex.partialX] using hd

private theorem fderivK_snd {θ : ℝ} (hθ : 0 < θ) (w : Plane) :
    fderiv ℝ (UnforcedLeray.B0284.heatKernel2 θ) w (0, 1) =
      (UnforcedLeray.B0296.gradHeatKernel2 θ w).2 := by
  have hp := UnforcedLeray.B0151.partialY_eq_fderiv (hkDiff2 θ) w
  rw [← hp]
  have hd := (UnforcedLeray.B0296.hasDerivAt_heatKernel2_snd hθ.ne' w).deriv
  simpa [UnforcedLeray.B0284.heatKernel2, UnforcedLeray.GaussianVortex.partialY] using hd

/-- Transfer the actual Gaussian age derivative onto the Laplacian of a bounded smooth field. -/
theorem integral_heatKernel2AgeDerivative_mul_comp_sub {θ : ℝ} (hθ : 0 < θ)
    {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfBound : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖f x‖ ≤ M)
    (hfDerivBound : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖fderiv ℝ f x‖ ≤ M)
    (hfSecondQBound : ∃ M : ℝ, 0 ≤ M ∧ ∀ x,
      ‖fderiv ℝ (fun y => fderiv ℝ f y (1, 0)) x‖ ≤ M)
    (hfSecondEtaBound : ∃ M : ℝ, 0 ≤ M ∧ ∀ x,
      ‖fderiv ℝ (fun y => fderiv ℝ f y (0, 1)) x‖ ≤ M)
    (z : Plane) :
    ∫ w : Plane, UnforcedLeray.HeatCylinder.heatKernel2AgeDerivative θ w * f (z - w) =
      ∫ w : Plane, UnforcedLeray.B0284.heatKernel2 θ w *
        UnforcedLeray.Train.lapS f (z - w) := by
  let K : Plane → ℝ := UnforcedLeray.B0284.heatKernel2 θ
  let Gq : Plane → ℝ := fun x => fderiv ℝ f x (1, 0)
  let Ge : Plane → ℝ := fun x => fderiv ℝ f x (0, 1)
  have hK : ContDiff ℝ ∞ K := by
    dsimp [K]
    change ContDiff ℝ ∞ (fun w : Plane =>
      UnforcedLeray.B0191.heatKernel 1 θ w.1 *
        UnforcedLeray.B0191.heatKernel 1 θ w.2)
    exact ((hkCD θ).comp contDiff_fst).mul
      ((hkCD θ).comp contDiff_snd)
  have hKq : Integrable (fun w : Plane =>
      (UnforcedLeray.B0296.gradHeatKernel2 θ w).1) :=
    (UnforcedLeray.B0296.integrable_dHeatKernel hθ).mul_prod
      (UnforcedLeray.B0296.integrable_heatKernel1 hθ)
  have hKe : Integrable (fun w : Plane =>
      (UnforcedLeray.B0296.gradHeatKernel2 θ w).2) :=
    (UnforcedLeray.B0296.integrable_heatKernel1 hθ).mul_prod
      (UnforcedLeray.B0296.integrable_dHeatKernel hθ)
  have hqSmooth : ContDiff ℝ ∞ Gq := by
    dsimp [Gq]
    exact (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have heSmooth : ContDiff ℝ ∞ Ge := by
    dsimp [Ge]
    exact (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  obtain ⟨M, hM, hfb⟩ := id hfBound
  obtain ⟨N, hN, hfdb⟩ := id hfDerivBound
  have hqBound : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖Gq x‖ ≤ M := by
    refine ⟨N, hN, ?_⟩
    intro x
    dsimp [Gq]
    calc
      ‖fderiv ℝ f x (1, 0)‖ ≤ ‖fderiv ℝ f x‖ * ‖((1 : ℝ), (0 : ℝ))‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ N := by simpa using hfdb x
  have heBound : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖Ge x‖ ≤ M := by
    refine ⟨N, hN, ?_⟩
    intro x
    dsimp [Ge]
    calc
      ‖fderiv ℝ f x (0, 1)‖ ≤ ‖fderiv ℝ f x‖ * ‖((0 : ℝ), (1 : ℝ))‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ N := by simpa using hfdb x
  obtain ⟨Nq, hNq, hqdb⟩ := hfSecondQBound
  obtain ⟨Ne, hNe, hedb⟩ := hfSecondEtaBound
  have hqDerivBound : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖fderiv ℝ Gq x‖ ≤ M := by
    exact ⟨Nq, hNq, by simpa [Gq] using hqdb⟩
  have heDerivBound : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖fderiv ℝ Ge x‖ ≤ M := by
    exact ⟨Ne, hNe, by simpa [Ge] using hedb⟩
  have hqFirstDeriv (w : Plane) :
      fderiv ℝ (fun y : Plane => (UnforcedLeray.B0296.gradHeatKernel2 θ y).1) w (1, 0) =
        partialX (fun y : Plane => (UnforcedLeray.B0296.gradHeatKernel2 θ y).1) w := by
    have hd : Differentiable ℝ (fun y : Plane => (UnforcedLeray.B0296.gradHeatKernel2 θ y).1) := gradFst_diff θ
    have _hd0 : True := by
      trivial
    exact (UnforcedLeray.B0151.partialX_eq_fderiv hd w).symm
  have heFirstDeriv (w : Plane) :
      fderiv ℝ (fun y : Plane => (UnforcedLeray.B0296.gradHeatKernel2 θ y).2) w (0, 1) =
        partialY (fun y : Plane => (UnforcedLeray.B0296.gradHeatKernel2 θ y).2) w := by
    have hd : Differentiable ℝ (fun y : Plane => (UnforcedLeray.B0296.gradHeatKernel2 θ y).2) := gradSnd_diff θ
    have _hd0 : True := by
      trivial
    exact (UnforcedLeray.B0151.partialY_eq_fderiv hd w).symm
  have hGqDeriv (w : Plane) :
      fderiv ℝ (fun y : Plane => f (z - y)) w (1, 0) = -Gq (z - w) := by
    have hmap : HasFDerivAt (fun y : Plane => z - y)
        (-ContinuousLinearMap.id ℝ Plane) w := (hasFDerivAt_id w).const_sub z
    have hcomp := (hf.differentiable (by simp) (z - w)).hasFDerivAt.comp w hmap
    change fderiv ℝ (f ∘ (fun y : Plane => z - y)) w (1, 0) = _
    rw [hcomp.fderiv]
    simp [Gq]
  have hGeDeriv (w : Plane) :
      fderiv ℝ (fun y : Plane => f (z - y)) w (0, 1) = -Ge (z - w) := by
    have hmap : HasFDerivAt (fun y : Plane => z - y)
        (-ContinuousLinearMap.id ℝ Plane) w := (hasFDerivAt_id w).const_sub z
    have hcomp := (hf.differentiable (by simp) (z - w)).hasFDerivAt.comp w hmap
    change fderiv ℝ (f ∘ (fun y : Plane => z - y)) w (0, 1) = _
    rw [hcomp.fderiv]
    simp [Ge]
  have hqK2Int : Integrable (fun w : Plane =>
      partialX (fun y : Plane => (UnforcedLeray.B0296.gradHeatKernel2 θ y).1) w) := by
    refine (integrable_qSecondKernel hθ).congr (Filter.Eventually.of_forall fun w => ?_)
    exact (qSecondKernel hθ w).symm
  have heK2Int : Integrable (fun w : Plane =>
      partialY (fun y : Plane => (UnforcedLeray.B0296.gradHeatKernel2 θ y).2) w) := by
    refine (integrable_etaSecondKernel hθ).congr (Filter.Eventually.of_forall fun w => ?_)
    exact (etaSecondKernel hθ w).symm
  have hqSecondTransfer := integral_comp_sub_second_ibp
    (K₁ := fun y : Plane => (UnforcedLeray.B0296.gradHeatKernel2 θ y).1)
    (K₂ := fun y : Plane => partialX (fun v : Plane =>
      (UnforcedLeray.B0296.gradHeatKernel2 θ v).1) y)
    (f := f) (h := Gq) (1, 0) z (gradFst_diff θ) hKq hqK2Int hqFirstDeriv
    hf hfBound hqSmooth hqBound hGqDeriv
  have heSecondTransfer := integral_comp_sub_second_ibp
    (K₁ := fun y : Plane => (UnforcedLeray.B0296.gradHeatKernel2 θ y).2)
    (K₂ := fun y : Plane => partialY (fun v : Plane =>
      (UnforcedLeray.B0296.gradHeatKernel2 θ v).2) y)
    (f := f) (h := Ge) (0, 1) z (gradSnd_diff θ) hKe heK2Int heFirstDeriv
    hf hfBound heSmooth heBound hGeDeriv
  have hqFirstTransfer := integral_heatKernel2_fderiv_mul_comp_sub
    hθ hqSmooth hqBound hqDerivBound z (1, 0)
  have heFirstTransfer := integral_heatKernel2_fderiv_mul_comp_sub
    hθ heSmooth heBound heDerivBound z (0, 1)
  have hqFinal :
      ∫ w : Plane, partialX (fun y : Plane => (UnforcedLeray.B0296.gradHeatKernel2 θ y).1) w * f (z - w) =
        ∫ w : Plane, K w * partialX (partialX f) (z - w) := by
    calc
      _ = ∫ w, (UnforcedLeray.B0296.gradHeatKernel2 θ w).1 * Gq (z - w) := hqSecondTransfer
      _ = ∫ w, K w * fderiv ℝ Gq (z - w) (1, 0) :=
        (integral_congr_ae (Filter.Eventually.of_forall fun w => by
          rw [← fderivK_fst hθ w])).trans hqFirstTransfer
      _ = ∫ w, K w * partialX (partialX f) (z - w) := by
        apply integral_congr_ae
        filter_upwards with w
        have hfirst : Gq = partialX f := by
          funext x
          dsimp [Gq]
          exact (UnforcedLeray.B0151.partialX_eq_fderiv
            (hf.differentiable (by simp)) x).symm
        rw [show fderiv ℝ Gq (z - w) (1, 0) = partialX Gq (z - w) from
          (UnforcedLeray.B0151.partialX_eq_fderiv (hqSmooth.differentiable (by simp)) _).symm]
        rw [hfirst]
  have heFinal :
      ∫ w : Plane, partialY (fun y : Plane => (UnforcedLeray.B0296.gradHeatKernel2 θ y).2) w * f (z - w) =
        ∫ w : Plane, K w * partialY (partialY f) (z - w) := by
    calc
      _ = ∫ w, (UnforcedLeray.B0296.gradHeatKernel2 θ w).2 * Ge (z - w) := heSecondTransfer
      _ = ∫ w, K w * fderiv ℝ Ge (z - w) (0, 1) :=
        (integral_congr_ae (Filter.Eventually.of_forall fun w => by
          rw [← fderivK_snd hθ w])).trans heFirstTransfer
      _ = ∫ w, K w * partialY (partialY f) (z - w) := by
        apply integral_congr_ae
        filter_upwards with w
        have hfirst : Ge = partialY f := by
          funext x
          dsimp [Ge]
          exact (UnforcedLeray.B0151.partialY_eq_fderiv
            (hf.differentiable (by simp)) x).symm
        rw [show fderiv ℝ Ge (z - w) (0, 1) = partialY Ge (z - w) from
          (UnforcedLeray.B0151.partialY_eq_fderiv (heSmooth.differentiable (by simp)) _).symm]
        rw [hfirst]
  have hkA : ∀ w : Plane, UnforcedLeray.HeatCylinder.heatKernel2AgeDerivative θ w =
      partialX (fun y : Plane => (UnforcedLeray.B0296.gradHeatKernel2 θ y).1) w +
        partialY (fun y : Plane => (UnforcedLeray.B0296.gradHeatKernel2 θ y).2) w := by
    intro w
    have e1 : partialX (UnforcedLeray.B0284.heatKernel2 θ) =
        fun y : Plane => (UnforcedLeray.B0296.gradHeatKernel2 θ y).1 := by
      funext y
      rw [UnforcedLeray.B0151.partialX_eq_fderiv (hkDiff2 θ) y]
      exact fderivK_fst hθ y
    have e2 : partialY (UnforcedLeray.B0284.heatKernel2 θ) =
        fun y : Plane => (UnforcedLeray.B0296.gradHeatKernel2 θ y).2 := by
      funext y
      rw [UnforcedLeray.B0151.partialY_eq_fderiv (hkDiff2 θ) y]
      exact fderivK_snd hθ y
    rw [UnforcedLeray.TrainB.heatKernel2AgeDerivative_eq_lapS hθ w,
      UnforcedLeray.Train.lapS_eq, e1, e2]
  have hfcont : Continuous (fun w : Plane => f (z - w)) :=
    hf.continuous.comp (continuous_const.sub continuous_id)
  have hIq : Integrable (fun w : Plane =>
      partialX (fun y : Plane => (UnforcedLeray.B0296.gradHeatKernel2 θ y).1) w * f (z - w)) :=
    (hqK2Int.bdd_mul hfcont.aestronglyMeasurable (c := M)
      (Filter.Eventually.of_forall fun w => hfb (z - w))).congr
      (Filter.Eventually.of_forall fun w => mul_comm _ _)
  have hIe : Integrable (fun w : Plane =>
      partialY (fun y : Plane => (UnforcedLeray.B0296.gradHeatKernel2 θ y).2) w * f (z - w)) :=
    (heK2Int.bdd_mul hfcont.aestronglyMeasurable (c := M)
      (Filter.Eventually.of_forall fun w => hfb (z - w))).congr
      (Filter.Eventually.of_forall fun w => mul_comm _ _)
  have hKint : Integrable K := UnforcedLeray.B0284.integrable_heatKernel2 hθ
  obtain ⟨Nq', _, hNq'⟩ := hqDerivBound
  obtain ⟨Ne', _, hNe'⟩ := heDerivBound
  have hGqx : ∀ x, partialX Gq x = fderiv ℝ Gq x (1, 0) := fun x =>
    UnforcedLeray.B0151.partialX_eq_fderiv (hqSmooth.differentiable (by simp)) x
  have hGey : ∀ x, partialY Ge x = fderiv ℝ Ge x (0, 1) := fun x =>
    UnforcedLeray.B0151.partialY_eq_fderiv (heSmooth.differentiable (by simp)) x
  have hxx : partialX Gq = partialX (partialX f) := by
    have : Gq = partialX f := by
      funext x
      exact (UnforcedLeray.B0151.partialX_eq_fderiv (hf.differentiable (by simp)) x).symm
    rw [this]
  have hyy : partialY Ge = partialY (partialY f) := by
    have : Ge = partialY f := by
      funext x
      exact (UnforcedLeray.B0151.partialY_eq_fderiv (hf.differentiable (by simp)) x).symm
    rw [this]
  have hXXcont : Continuous (fun w : Plane => partialX (partialX f) (z - w)) := by
    rw [← hxx]
    have : Continuous (fun x => partialX Gq x) := by
      simp_rw [hGqx]
      exact (hqSmooth.continuous_fderiv (by simp)).clm_apply continuous_const
    exact this.comp (continuous_const.sub continuous_id)
  have hYYcont : Continuous (fun w : Plane => partialY (partialY f) (z - w)) := by
    rw [← hyy]
    have : Continuous (fun x => partialY Ge x) := by
      simp_rw [hGey]
      exact (heSmooth.continuous_fderiv (by simp)).clm_apply continuous_const
    exact this.comp (continuous_const.sub continuous_id)
  have hXXb : ∀ w : Plane, ‖partialX (partialX f) (z - w)‖ ≤ Nq' := by
    intro w
    rw [← hxx, hGqx]
    calc ‖fderiv ℝ Gq (z - w) (1, 0)‖ ≤ ‖fderiv ℝ Gq (z - w)‖ * ‖((1 : ℝ), (0 : ℝ))‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ Nq' := by simpa using hNq' (z - w)
  have hYYb : ∀ w : Plane, ‖partialY (partialY f) (z - w)‖ ≤ Ne' := by
    intro w
    rw [← hyy, hGey]
    calc ‖fderiv ℝ Ge (z - w) (0, 1)‖ ≤ ‖fderiv ℝ Ge (z - w)‖ * ‖((0 : ℝ), (1 : ℝ))‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ Ne' := by simpa using hNe' (z - w)
  have hJq : Integrable (fun w : Plane => K w * partialX (partialX f) (z - w)) :=
    (hKint.bdd_mul hXXcont.aestronglyMeasurable (c := Nq')
      (Filter.Eventually.of_forall hXXb)).congr
      (Filter.Eventually.of_forall fun w => mul_comm _ _)
  have hJe : Integrable (fun w : Plane => K w * partialY (partialY f) (z - w)) :=
    (hKint.bdd_mul hYYcont.aestronglyMeasurable (c := Ne')
      (Filter.Eventually.of_forall hYYb)).congr
      (Filter.Eventually.of_forall fun w => mul_comm _ _)
  calc ∫ w : Plane, UnforcedLeray.HeatCylinder.heatKernel2AgeDerivative θ w * f (z - w)
      = ∫ w : Plane, (partialX (fun y : Plane => (UnforcedLeray.B0296.gradHeatKernel2 θ y).1) w *
          f (z - w) + partialY (fun y : Plane =>
            (UnforcedLeray.B0296.gradHeatKernel2 θ y).2) w * f (z - w)) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
        dsimp only
        rw [hkA w]; ring
    _ = (∫ w : Plane, partialX (fun y : Plane =>
          (UnforcedLeray.B0296.gradHeatKernel2 θ y).1) w * f (z - w)) +
        ∫ w : Plane, partialY (fun y : Plane =>
          (UnforcedLeray.B0296.gradHeatKernel2 θ y).2) w * f (z - w) := integral_add hIq hIe
    _ = (∫ w : Plane, K w * partialX (partialX f) (z - w)) +
        ∫ w : Plane, K w * partialY (partialY f) (z - w) := by rw [hqFinal, heFinal]
    _ = ∫ w : Plane, (K w * partialX (partialX f) (z - w) +
        K w * partialY (partialY f) (z - w)) := (integral_add hJq hJe).symm
    _ = ∫ w : Plane, UnforcedLeray.B0284.heatKernel2 θ w *
        UnforcedLeray.Train.lapS f (z - w) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
        dsimp only
        rw [UnforcedLeray.Train.lapS_eq]; ring

end UnforcedLeray.Short.PartI.IBPLeaf

namespace UnforcedLeray.Short.PartI

open MeasureTheory
open UnforcedLeray.GaussianVortex (Plane)

private theorem leafIBP_kAge_even (θ : ℝ) (w : Plane) :
    UnforcedLeray.HeatCylinder.heatKernel2AgeDerivative θ (-w) =
      UnforcedLeray.HeatCylinder.heatKernel2AgeDerivative θ w := by
  obtain ⟨a, b⟩ := w
  simp [UnforcedLeray.HeatCylinder.heatKernel2AgeDerivative, UnforcedLeray.B0284.heatKernel2,
    UnforcedLeray.B0191.heatKernel, neg_sq]

private theorem leafIBP_k_even (θ : ℝ) (w : Plane) :
    UnforcedLeray.B0284.heatKernel2 θ (-w) = UnforcedLeray.B0284.heatKernel2 θ w := by
  obtain ⟨a, b⟩ := w
  simp [UnforcedLeray.B0284.heatKernel2, UnforcedLeray.B0191.heatKernel, neg_sq]

theorem leafAgeIBPCH_proof : UnforcedLeray.Short.PartI.LeafAgeIBPCH := by
  unfold UnforcedLeray.Short.PartI.LeafAgeIBPCH
  intro θ hθ f hf hfB hfD hfQ hfE
  have hfB' : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖f x‖ ≤ M := by
    obtain ⟨M, hM⟩ := hfB
    exact ⟨M, le_trans (norm_nonneg _) (hM 0), hM⟩
  have hfD' : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖fderiv ℝ f x‖ ≤ M := by
    obtain ⟨M, hM⟩ := hfD
    exact ⟨M, le_trans (norm_nonneg _) (hM 0), hM⟩
  have hfQ' : ∃ M : ℝ, 0 ≤ M ∧ ∀ x,
      ‖fderiv ℝ (fun y => fderiv ℝ f y (1, 0)) x‖ ≤ M := by
    obtain ⟨M, hM⟩ := hfQ
    exact ⟨M, le_trans (norm_nonneg _) (hM 0), hM⟩
  have hfE' : ∃ M : ℝ, 0 ≤ M ∧ ∀ x,
      ‖fderiv ℝ (fun y => fderiv ℝ f y (0, 1)) x‖ ≤ M := by
    obtain ⟨M, hM⟩ := hfE
    exact ⟨M, le_trans (norm_nonneg _) (hM 0), hM⟩
  have key := UnforcedLeray.Short.PartI.IBPLeaf.integral_heatKernel2AgeDerivative_mul_comp_sub
    hθ hf hfB' hfD' hfQ' hfE' 0
  simp only [zero_sub] at key
  have h1 : ∫ w : Plane, UnforcedLeray.HeatCylinder.heatKernel2AgeDerivative θ w * f (-w) =
      ∫ w : Plane, UnforcedLeray.HeatCylinder.heatKernel2AgeDerivative θ w * f w := by
    have h := integral_neg_eq_self
      (fun w : Plane => UnforcedLeray.HeatCylinder.heatKernel2AgeDerivative θ w * f w) volume
    simp only [leafIBP_kAge_even] at h
    exact h
  have h2 : ∫ w : Plane, UnforcedLeray.B0284.heatKernel2 θ w * UnforcedLeray.Train.lapS f (-w) =
      ∫ w : Plane, UnforcedLeray.B0284.heatKernel2 θ w * UnforcedLeray.Train.lapS f w := by
    have h := integral_neg_eq_self
      (fun w : Plane => UnforcedLeray.B0284.heatKernel2 θ w * UnforcedLeray.Train.lapS f w) volume
    simp only [leafIBP_k_even] at h
    exact h
  rw [← h1, ← h2]
  exact key

end UnforcedLeray.Short.PartI
