import UnforcedLeray.Lib.TrainB.DatumHeatH3
import UnforcedLeray.Lib.TrainB.InitialDatumDerivativeSolenoidal
import UnforcedLeray.Lib.HeatCylinder.HeatVecDerivative

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory
open scoped ContDiff

namespace UnforcedLeray.TrainB

open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.Train (Vec)

private theorem heatVecConvolution_coord {θ : ℝ} (hθ : 0 < θ)
    {F : Plane → Vec} (hF : Continuous F)
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ x, ‖F x‖ ≤ M)
    (z : Plane) (i : Fin 2) :
    (HeatCylinder.heatVecConvolution θ F z) i =
      ∫ w : Plane, B0284.heatKernel2 θ w * F (z - w) i := by
  have hkernel : Integrable (B0284.heatKernel2 θ) := B0284.integrable_heatKernel2 hθ
  have hcont : Continuous (fun w : Plane => B0284.heatKernel2 θ w • F (z - w)) := by
    have hk : Continuous (B0284.heatKernel2 θ) := by
      unfold B0284.heatKernel2 B0191.heatKernel
      fun_prop
    exact hk.smul (hF.comp (continuous_const.sub continuous_id))
  have hint : Integrable (fun w : Plane => B0284.heatKernel2 θ w • F (z - w)) := by
    refine Integrable.mono' (hkernel.mul_const M) hcont.aestronglyMeasurable ?_
    filter_upwards [] with w
    calc
      ‖B0284.heatKernel2 θ w • F (z - w)‖ ≤
          ‖B0284.heatKernel2 θ w‖ * ‖F (z - w)‖ := by rw [norm_smul]
      _ ≤ B0284.heatKernel2 θ w * M := by
        rw [Real.norm_eq_abs, abs_of_nonneg (B0284.heatKernel2_nonneg hθ w)]
        exact mul_le_mul_of_nonneg_left (hbound _) (B0284.heatKernel2_nonneg hθ w)
  let L : Vec →L[ℝ] ℝ := EuclideanSpace.proj i
  calc
    (HeatCylinder.heatVecConvolution θ F z) i = L (∫ w : Plane,
        B0284.heatKernel2 θ w • F (z - w)) := rfl
    _ = ∫ w : Plane, L (B0284.heatKernel2 θ w • F (z - w)) :=
      (L.integral_comp_comm hint).symm
    _ = ∫ w : Plane, B0284.heatKernel2 θ w * F (z - w) i := by
      congr 1

/-- The literal vector Gaussian convolution preserves pointwise zero divergence for smooth
bounded periodic cylinder fields. -/
theorem divergence_heatVecConvolution_eq_zero {c θ : ℝ} (hθ : 0 < θ)
    {F : Plane → Vec} (hF : ContDiff ℝ ∞ F)
    (hFbound : ∃ M : ℝ, ∀ z, ‖F z‖ ≤ M)
    (hDbound : ∃ M : ℝ, ∀ z, ‖fderiv ℝ F z‖ ≤ M)
    (hdiv : ∀ z, Cyl.divergence F z = 0) (z : Plane) :
    Cyl.divergence (HeatCylinder.heatVecConvolution θ F) z = 0 := by
  obtain ⟨M₀, hM₀⟩ := hFbound
  obtain ⟨M₁, hM₁⟩ := hDbound
  have hF1 : ContDiff ℝ 1 F := hF.of_le (by norm_num)
  have hdiff : Differentiable ℝ (HeatCylinder.heatVecConvolution θ F) := by
    intro x
    exact (HeatCylinder.hasFDerivAt_heatVecConvolution hθ hF1 hM₀ hM₁ x).differentiableAt
  let eQ : Plane := (1, 0)
  let eEta : Plane := (0, 1)
  let Dq : Plane → Vec := fun x => fderiv ℝ F x eQ
  let De : Plane → Vec := fun x => fderiv ℝ F x eEta
  have hDqCont : Continuous Dq := by
    exact ((hF.continuous_fderiv (by simp)).clm_apply continuous_const)
  have hDeCont : Continuous De := by
    exact ((hF.continuous_fderiv (by simp)).clm_apply continuous_const)
  have hM₁' : 0 ≤ M₁ := (norm_nonneg _).trans (hM₁ 0)
  have hDqBound : ∀ x, ‖Dq x‖ ≤ M₁ := by
    intro x
    calc
      ‖fderiv ℝ F x eQ‖ ≤ ‖fderiv ℝ F x‖ * ‖eQ‖ :=
        (fderiv ℝ F x).le_opNorm _
      _ = ‖fderiv ℝ F x‖ := by norm_num [eQ, Plane]
      _ ≤ M₁ := hM₁ x
  have hDeBound : ∀ x, ‖De x‖ ≤ M₁ := by
    intro x
    calc
      ‖fderiv ℝ F x eEta‖ ≤ ‖fderiv ℝ F x‖ * ‖eEta‖ :=
        (fderiv ℝ F x).le_opNorm _
      _ = ‖fderiv ℝ F x‖ := by norm_num [eEta, Plane]
      _ ≤ M₁ := hM₁ x
  let H : Plane → Vec := HeatCylinder.heatVecConvolution θ F
  let L₀ : Vec →L[ℝ] ℝ := EuclideanSpace.proj 0
  let L₁ : Vec →L[ℝ] ℝ := EuclideanSpace.proj 1
  have hcomp (i : Fin 2) (x e : Plane) :
      (fderiv ℝ H x e) i = fderiv ℝ (fun y => H y i) x e := by
    let L : Vec →L[ℝ] ℝ := EuclideanSpace.proj i
    have hc := fderiv_comp x L.differentiableAt (hdiff x)
    rw [L.fderiv] at hc
    have hv := congrArg (fun A : Plane →L[ℝ] ℝ => A e) hc
    have hcompFun : (L ∘ H) = fun y => H y i := by
      funext y
      rfl
    rw [hcompFun] at hv
    simpa [L] using hv.symm
  have hFcomp (i : Fin 2) (x e : Plane) :
      (fderiv ℝ F x e) i = fderiv ℝ (fun y => F y i) x e := by
    let L : Vec →L[ℝ] ℝ := EuclideanSpace.proj i
    have hc := fderiv_comp x L.differentiableAt ((hF.differentiable (by simp)) x)
    rw [L.fderiv] at hc
    have hv := congrArg (fun A : Plane →L[ℝ] ℝ => A e) hc
    have hcompFun : (L ∘ F) = fun y => F y i := by
      funext y
      rfl
    rw [hcompFun] at hv
    simpa [L] using hv.symm
  have hHcoord (i : Fin 2) : (fun y => H y i) = (EuclideanSpace.proj i) ∘ H := by
    funext y
    rfl
  have hHcoordDiff (i : Fin 2) : Differentiable ℝ (fun y => H y i) := by
    rw [hHcoord i]
    exact (EuclideanSpace.proj i).differentiable.comp hdiff
  have hq : Cyl.partialQ (fun y => H y 0) z =
      HeatCylinder.heatVecConvolution θ Dq z 0 := by
    change Cyl.partialQ ((EuclideanSpace.proj 0) ∘ H) z = _
    rw [← hHcoord 0]
    rw [Cyl.partialQ_eq_fderiv (hHcoordDiff 0) z]
    rw [← hcomp 0 z eQ]
    rw [HeatCylinder.fderiv_heatVecConvolution_apply_of_bounds hθ hF1 hM₀ hM₁ z eQ]
  have he : Cyl.partialEta (fun y => H y 1) z =
      HeatCylinder.heatVecConvolution θ De z 1 := by
    change Cyl.partialEta ((EuclideanSpace.proj 1) ∘ H) z = _
    rw [← hHcoord 1]
    rw [Cyl.partialEta_eq_fderiv (hHcoordDiff 1) z]
    rw [← hcomp 1 z eEta]
    rw [HeatCylinder.fderiv_heatVecConvolution_apply_of_bounds hθ hF1 hM₀ hM₁ z eEta]
  have hqBound : ∀ x, |Cyl.partialQ (fun y => F y 0) x| ≤ M₁ := by
    intro x
    have hd0 : Differentiable ℝ (fun y => F y 0) := by
      change Differentiable ℝ ((EuclideanSpace.proj 0) ∘ F)
      exact (EuclideanSpace.proj 0).differentiable.comp (hF.differentiable (by simp))
    rw [Cyl.partialQ_eq_fderiv hd0 x]
    rw [← hFcomp 0 x eQ]
    calc
      |(fderiv ℝ F x eQ) 0| =
          ‖(fderiv ℝ F x eQ) 0‖ := by rw [Real.norm_eq_abs]
      _ ≤ ‖fderiv ℝ F x eQ‖ := PiLp.norm_apply_le _ _
      _ ≤ ‖fderiv ℝ F x‖ * ‖eQ‖ :=
        (fderiv ℝ F x).le_opNorm _
      _ = ‖fderiv ℝ F x‖ := by norm_num [eQ, eEta, Plane]
      _ ≤ M₁ := hM₁ x
  have heBound : ∀ x, |Cyl.partialEta (fun y => F y 1) x| ≤ M₁ := by
    intro x
    have hd1 : Differentiable ℝ (fun y => F y 1) := by
      change Differentiable ℝ ((EuclideanSpace.proj 1) ∘ F)
      exact (EuclideanSpace.proj 1).differentiable.comp (hF.differentiable (by simp))
    rw [Cyl.partialEta_eq_fderiv hd1 x]
    rw [← hFcomp 1 x eEta]
    calc
      |(fderiv ℝ F x eEta) 1| =
          ‖(fderiv ℝ F x eEta) 1‖ := by rw [Real.norm_eq_abs]
      _ ≤ ‖fderiv ℝ F x eEta‖ := PiLp.norm_apply_le _ _
      _ ≤ ‖fderiv ℝ F x‖ * ‖eEta‖ :=
        (fderiv ℝ F x).le_opNorm _
      _ = ‖fderiv ℝ F x‖ := by norm_num [eQ, eEta, Plane]
      _ ≤ M₁ := hM₁ x
  have hkernel : Integrable (B0284.heatKernel2 θ) := B0284.integrable_heatKernel2 hθ
  have hkernelCont : Continuous (B0284.heatKernel2 θ) := by
    unfold B0284.heatKernel2 B0191.heatKernel
    fun_prop
  have hqfunCont : Continuous (Cyl.partialQ (fun y => F y 0)) := by
    have hD : ContDiff ℝ ∞ (fun y => F y 0) := by
      change ContDiff ℝ ∞ ((EuclideanSpace.proj 0) ∘ F)
      exact (EuclideanSpace.proj 0).contDiff.comp hF
    exact (Cyl.contDiff_partialQ (n := (0 : WithTop ℕ∞))
      (hD.of_le (by norm_num))).continuous
  have hefunCont : Continuous (Cyl.partialEta (fun y => F y 1)) := by
    have hD : ContDiff ℝ ∞ (fun y => F y 1) := by
      change ContDiff ℝ ∞ ((EuclideanSpace.proj 1) ∘ F)
      exact (EuclideanSpace.proj 1).contDiff.comp hF
    exact (Cyl.contDiff_partialEta (n := (0 : WithTop ℕ∞))
      (hD.of_le (by norm_num))).continuous
  have hqcont : Continuous (fun w : Plane => B0284.heatKernel2 θ w *
      Cyl.partialQ (fun y => F y 0) (z - w)) :=
    hkernelCont.mul (hqfunCont.comp (continuous_const.sub continuous_id))
  have hecont : Continuous (fun w : Plane => B0284.heatKernel2 θ w *
      Cyl.partialEta (fun y => F y 1) (z - w)) :=
    hkernelCont.mul (hefunCont.comp (continuous_const.sub continuous_id))
  have hqInt : Integrable (fun w : Plane => B0284.heatKernel2 θ w *
      Cyl.partialQ (fun y => F y 0) (z - w)) := by
    refine Integrable.mono' (hkernel.mul_const M₁) hqcont.aestronglyMeasurable ?_
    filter_upwards [] with w
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (B0284.heatKernel2_nonneg hθ w)]
    exact mul_le_mul_of_nonneg_left (hqBound (z - w)) (B0284.heatKernel2_nonneg hθ w)
  have heInt : Integrable (fun w : Plane => B0284.heatKernel2 θ w *
      Cyl.partialEta (fun y => F y 1) (z - w)) := by
    refine Integrable.mono' (hkernel.mul_const M₁) hecont.aestronglyMeasurable ?_
    filter_upwards [] with w
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (B0284.heatKernel2_nonneg hθ w)]
    exact mul_le_mul_of_nonneg_left (heBound (z - w)) (B0284.heatKernel2_nonneg hθ w)
  have hzero : (fun w : Plane => B0284.heatKernel2 θ w *
      (Cyl.partialQ (fun x => F x 0) (z - w) +
        Cyl.partialEta (fun x => F x 1) (z - w))) = fun _ => 0 := by
    funext w
    change B0284.heatKernel2 θ w * Cyl.divergence F (z - w) = 0
    rw [hdiv]
    simp
  rw [Cyl.divergence, hq, he]
  rw [heatVecConvolution_coord hθ hDqCont hM₁' hDqBound,
    heatVecConvolution_coord hθ hDeCont hM₁' hDeBound]
  have hd0 : Differentiable ℝ (fun y => F y 0) := by
    change Differentiable ℝ ((EuclideanSpace.proj 0) ∘ F)
    exact (EuclideanSpace.proj 0).differentiable.comp (hF.differentiable (by simp))
  have hd1 : Differentiable ℝ (fun y => F y 1) := by
    change Differentiable ℝ ((EuclideanSpace.proj 1) ∘ F)
    exact (EuclideanSpace.proj 1).differentiable.comp (hF.differentiable (by simp))
  have hqInputEq (x : Plane) : Dq x 0 = Cyl.partialQ (fun y => F y 0) x := by
    rw [Cyl.partialQ_eq_fderiv hd0 x]
    rw [← hFcomp 0 x eQ]
  have heInputEq (x : Plane) : De x 1 = Cyl.partialEta (fun y => F y 1) x := by
    rw [Cyl.partialEta_eq_fderiv hd1 x]
    rw [← hFcomp 1 x eEta]
  have hqIntegralEq :
      (∫ w : Plane, B0284.heatKernel2 θ w * Dq (z - w) 0) =
        ∫ w : Plane, B0284.heatKernel2 θ w * Cyl.partialQ (fun y => F y 0) (z - w) := by
    apply integral_congr_ae
    filter_upwards [] with w
    rw [hqInputEq]
  have heIntegralEq :
      (∫ w : Plane, B0284.heatKernel2 θ w * De (z - w) 1) =
        ∫ w : Plane, B0284.heatKernel2 θ w * Cyl.partialEta (fun y => F y 1) (z - w) := by
    apply integral_congr_ae
    filter_upwards [] with w
    rw [heInputEq]
  rw [hqIntegralEq, heIntegralEq]
  rw [← integral_add hqInt heInt]
  have hfactor :
      (fun w : Plane => B0284.heatKernel2 θ w *
        Cyl.partialQ (fun x => F x 0) (z - w) +
        B0284.heatKernel2 θ w * Cyl.partialEta (fun x => F x 1) (z - w)) =
      (fun w : Plane => B0284.heatKernel2 θ w *
        (Cyl.partialQ (fun x => F x 0) (z - w) +
          Cyl.partialEta (fun x => F x 1) (z - w))) := by
    funext w
    ring
  rw [hfactor]
  rw [hzero]
  simp

/-- Every ordered derivative of the actual Gaussian Train datum remains pointwise
divergence-free after heat evolution. -/
theorem datum_iterD_heatVecConvolution_divergence_zero {c θ : ℝ}
    (hc : 2 ≤ c) (hθ : 0 < θ) (vs : List Plane) :
    ∀ z, Cyl.divergence
      (HeatCylinder.heatVecConvolution θ (Sob.iterD vs (Train.datum c))) z = 0 := by
  intro z
  exact divergence_heatVecConvolution_eq_zero (c := c) hθ
    (Sob.contDiff_iterD (Train.datum_contDiff (by linarith : c ≠ 0)) vs)
    (datum_iterD_global_bound hc vs)
    (datum_fderiv_iterD_global_bound hc vs)
    (datum_iterD_divergence_zero (by linarith : c ≠ 0) vs) z

end UnforcedLeray.TrainB

#print axioms UnforcedLeray.TrainB.divergence_heatVecConvolution_eq_zero
#print axioms UnforcedLeray.TrainB.datum_iterD_heatVecConvolution_divergence_zero
