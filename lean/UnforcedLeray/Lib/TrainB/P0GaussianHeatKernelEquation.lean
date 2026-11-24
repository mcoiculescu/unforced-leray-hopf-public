import UnforcedLeray.Lib.HeatCylinder.HeatKernelAgeDerivative
import UnforcedLeray.Units.B0296.Kernel
import UnforcedLeray.Units.B0151.DivCurl
import UnforcedLeray.Lib.Train.Ops

/-! The actual planar heat kernel satisfies the heat equation at every positive age. -/
set_option autoImplicit false
noncomputable section

namespace UnforcedLeray.TrainB

open UnforcedLeray.GaussianVortex (Plane partialX partialY)

private theorem deriv_dHeatKernel_formula {θ x : ℝ} (hθ : θ ≠ 0) :
    deriv (UnforcedLeray.B0296.dHeatKernel θ) x =
      ((x ^ 2 / (4 * θ ^ 2)) - 1 / (2 * θ)) *
        UnforcedLeray.B0191.heatKernel 1 θ x := by
  have hcoef : (fun y : ℝ => -(y / (2 * θ))) =
      fun y => (-(1 / (2 * θ))) * y := by
    funext y
    ring
  unfold UnforcedLeray.B0296.dHeatKernel
  change deriv ((fun y : ℝ => -(y / (2 * θ))) *
    (UnforcedLeray.B0191.heatKernel 1 θ)) x = _
  have hcoefDiff : DifferentiableAt ℝ (fun y : ℝ => -(y / (2 * θ))) x := by fun_prop
  have hkernelDiff : DifferentiableAt ℝ (UnforcedLeray.B0191.heatKernel 1 θ) x :=
    ((UnforcedLeray.B0191.contDiff_heatKernel 1 θ).differentiable (by simp)).differentiableAt
  rw [deriv_mul hcoefDiff hkernelDiff]
  rw [hcoef, deriv_const_mul_id]
  rw [(UnforcedLeray.B0296.hasDerivAt_heatKernel hθ x).deriv]
  rw [UnforcedLeray.B0296.dHeatKernel]
  field_simp [hθ]
  ring

/-- Positive-age kernel heat equation for the actual B0284 product Gaussian. -/
theorem heatKernel2AgeDerivative_eq_lapS {θ : ℝ} (hθ : 0 < θ) (w : Plane) :
    UnforcedLeray.HeatCylinder.heatKernel2AgeDerivative θ w =
      UnforcedLeray.Train.lapS (UnforcedLeray.B0284.heatKernel2 θ) w := by
  have hθ0 : θ ≠ 0 := hθ.ne'
  have hqFirst : ∀ w : Plane,
      partialX (UnforcedLeray.B0284.heatKernel2 θ) w =
        UnforcedLeray.B0296.dHeatKernel θ w.1 *
          UnforcedLeray.B0191.heatKernel 1 θ w.2 := by
    intro ⟨q, η⟩
    exact (UnforcedLeray.B0296.hasDerivAt_heatKernel2_fst hθ0 (q, η)).deriv
  have hηFirst : ∀ w : Plane,
      partialY (UnforcedLeray.B0284.heatKernel2 θ) w =
        UnforcedLeray.B0191.heatKernel 1 θ w.1 *
          UnforcedLeray.B0296.dHeatKernel θ w.2 := by
    intro ⟨q, η⟩
    exact (UnforcedLeray.B0296.hasDerivAt_heatKernel2_snd hθ0 (q, η)).deriv
  have hqSecond (w : Plane) :
      partialX (partialX (UnforcedLeray.B0284.heatKernel2 θ)) w =
        ((w.1 ^ 2 / (4 * θ ^ 2) - 1 / (2 * θ)) *
          UnforcedLeray.B0191.heatKernel 1 θ w.1) *
            UnforcedLeray.B0191.heatKernel 1 θ w.2 := by
    rcases w with ⟨q, η⟩
    rw [funext hqFirst]
    change deriv (fun x : ℝ => UnforcedLeray.B0296.dHeatKernel θ x *
      UnforcedLeray.B0191.heatKernel 1 θ η) q = _
    rw [deriv_mul_const_field]
    rw [deriv_dHeatKernel_formula hθ0]
  have hηSecond (w : Plane) :
      partialY (partialY (UnforcedLeray.B0284.heatKernel2 θ)) w =
        (UnforcedLeray.B0191.heatKernel 1 θ w.1 *
          ((w.2 ^ 2 / (4 * θ ^ 2) - 1 / (2 * θ)) *
            UnforcedLeray.B0191.heatKernel 1 θ w.2)) := by
    rcases w with ⟨q, η⟩
    rw [funext hηFirst]
    change deriv (fun y : ℝ => UnforcedLeray.B0191.heatKernel 1 θ q *
      UnforcedLeray.B0296.dHeatKernel θ y) η = _
    rw [deriv_const_mul_field]
    rw [deriv_dHeatKernel_formula hθ0]
  rw [UnforcedLeray.Train.lapS_eq]
  rw [hqSecond, hηSecond]
  unfold UnforcedLeray.HeatCylinder.heatKernel2AgeDerivative
    UnforcedLeray.B0284.heatKernel2
  simp only [UnforcedLeray.B0191.heatKernel]
  ring

#print axioms UnforcedLeray.TrainB.heatKernel2AgeDerivative_eq_lapS
end UnforcedLeray.TrainB
