import UnforcedLeray.Lib.HeatCylinder.HeatVecDerivative

/-!
# Iterated derivative commutation for actual vector heat

The first Fréchet derivative commutation iterates through the classical Sobolev derivative words
of any smooth periodic compact-axial input. The output itself is allowed its Gaussian axial tails.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.Train (Vec)

/-- Every ordered classical derivative word commutes with the actual Euclidean-vector Gaussian
heat convolution on a smooth cylinder input. -/
theorem iterD_heatVecConvolution_commute {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    {T : Plane → Vec} (hT : UnforcedLeray.Sob.IsCylSmooth c T) (vs : List Plane) :
    UnforcedLeray.Sob.iterD vs (heatVecConvolution θ T) =
      heatVecConvolution θ (UnforcedLeray.Sob.iterD vs T) := by
  induction vs with
  | nil => rfl
  | cons e vs ih =>
      funext z
      change fderiv ℝ (UnforcedLeray.Sob.iterD vs (heatVecConvolution θ T)) z e =
        heatVecConvolution θ (UnforcedLeray.Sob.iterD (e :: vs) T) z
      rw [ih]
      rw [fderiv_heatVecConvolution_apply hc hθ (hT.iterD vs) z e]
      rfl

/-- The actual vector heat of a smooth cylinder field is differentiable everywhere. -/
theorem differentiable_heatVecConvolution_of_cylSmooth {c θ : ℝ} (hc : 0 < c)
    (hθ : 0 < θ) {T : Plane → Vec} (hT : UnforcedLeray.Sob.IsCylSmooth c T) :
    Differentiable ℝ (heatVecConvolution θ T) := by
  obtain ⟨M₀, _, hTbound⟩ :=
    UnforcedLeray.HeatCylinder.exists_global_bound_of_cylSmooth hc hT
  obtain ⟨M₁, _, hderivBound⟩ :=
    UnforcedLeray.HeatCylinder.exists_global_deriv_bound_of_cylSmooth hc hT
  have hT1 : ContDiff ℝ 1 T := hT.smooth.of_le (by norm_num)
  intro z
  exact (hasFDerivAt_heatVecConvolution hθ hT1 hTbound hderivBound z).differentiableAt

/-- The actual vector heat output of a periodic smooth input is periodic. -/
theorem heatVecConvolution_periodic {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    {T : Plane → Vec} (hT : UnforcedLeray.Sob.IsCylSmooth c T) :
    UnforcedLeray.Cyl.IsPeriodic c (heatVecConvolution θ T) := by
  intro z
  let f : Plane → Plane := fun x => UnforcedLeray.Train.toVecL.symm (T x)
  have hper : UnforcedLeray.B0284.IsQPeriodic c f := by
    intro x
    have hx : (x.1 + c, x.2) = x + (c, 0) := by ext <;> simp
    rw [hx]
    change UnforcedLeray.Train.toVecL.symm (T (x + (c, 0))) =
      UnforcedLeray.Train.toVecL.symm (T x)
    rw [hT.periodic x]
  have hperiodic := UnforcedLeray.B0284.heat_periodic (c := c) (θ := θ) (f := f) hper
  have hconvert (x : Plane) : heatVecConvolution θ T x =
      UnforcedLeray.Train.toVec (UnforcedLeray.B0284.heat θ f x) := by
    rw [heatVecConvolution, UnforcedLeray.B0284.heat_apply_of_pos hθ]
    let L : Plane →L[ℝ] Vec := UnforcedLeray.Train.toVecL
    have hint : Integrable (fun w : Plane =>
        UnforcedLeray.B0284.heatKernel2 θ w • f (x - w)) := by
      have hkernel : Continuous (fun w : Plane => UnforcedLeray.B0284.heatKernel2 θ w) := by
        unfold UnforcedLeray.B0284.heatKernel2 UnforcedLeray.B0191.heatKernel
        fun_prop
      have hf : Continuous (fun w : Plane => f (x - w)) := by
        let Linv : Vec →L[ℝ] Plane := UnforcedLeray.Train.toVecL.symm.toContinuousLinearMap
        change Continuous (fun w : Plane => Linv (T (x - w)))
        exact Linv.continuous.comp (hT.smooth.continuous.comp
          (continuous_const.sub continuous_id))
      have hcontinuous : Continuous (fun w : Plane =>
          UnforcedLeray.B0284.heatKernel2 θ w • f (x - w)) := hkernel.smul hf
      obtain ⟨M₀, hM₀, hTbound⟩ :=
        UnforcedLeray.HeatCylinder.exists_global_bound_of_cylSmooth hc hT
      let Linv : Vec →L[ℝ] Plane := UnforcedLeray.Train.toVecL.symm.toContinuousLinearMap
      let M : ℝ := ‖Linv‖ * M₀
      refine Integrable.mono' ((UnforcedLeray.B0284.integrable_heatKernel2 hθ).mul_const M)
        hcontinuous.aestronglyMeasurable ?_
      filter_upwards [] with w
      calc
        ‖UnforcedLeray.B0284.heatKernel2 θ w • f (x - w)‖ ≤
            |UnforcedLeray.B0284.heatKernel2 θ w| * ‖f (x - w)‖ := by
          simp only [norm_smul, Real.norm_eq_abs]
          exact le_rfl
        _ ≤ UnforcedLeray.B0284.heatKernel2 θ w * M := by
          rw [abs_of_nonneg (UnforcedLeray.B0284.heatKernel2_nonneg hθ w)]
          apply mul_le_mul_of_nonneg_left _
            (UnforcedLeray.B0284.heatKernel2_nonneg hθ w)
          change ‖Linv (T (x - w))‖ ≤ M
          calc
            ‖Linv (T (x - w))‖ ≤ ‖Linv‖ * ‖T (x - w)‖ := Linv.le_opNorm _
            _ ≤ M := by
              dsimp [M]
              exact mul_le_mul_of_nonneg_left (hTbound (x - w)) (norm_nonneg _)
    calc
      (∫ w : Plane, UnforcedLeray.B0284.heatKernel2 θ w • T (x - w)) =
          ∫ w : Plane, L (UnforcedLeray.B0284.heatKernel2 θ w • f (x - w)) := by
        congr 1
        funext w
        change UnforcedLeray.B0284.heatKernel2 θ w • T (x - w) =
          L (UnforcedLeray.B0284.heatKernel2 θ w •
            UnforcedLeray.Train.toVecL.symm (T (x - w)))
        rw [map_smul]
        change UnforcedLeray.B0284.heatKernel2 θ w • T (x - w) =
          UnforcedLeray.B0284.heatKernel2 θ w •
            UnforcedLeray.Train.toVecL
              (UnforcedLeray.Train.toVecL.symm (T (x - w)))
        rw [UnforcedLeray.Train.toVecL.apply_symm_apply]
      _ = L (∫ w : Plane, UnforcedLeray.B0284.heatKernel2 θ w • f (x - w)) :=
        L.integral_comp_comm hint
  rw [hconvert (z.1 + c, z.2), hconvert z]
  exact congrArg UnforcedLeray.Train.toVec (hperiodic z)

end UnforcedLeray.HeatCylinder

#print axioms UnforcedLeray.HeatCylinder.iterD_heatVecConvolution_commute
#print axioms UnforcedLeray.HeatCylinder.differentiable_heatVecConvolution_of_cylSmooth
#print axioms UnforcedLeray.HeatCylinder.heatVecConvolution_periodic
