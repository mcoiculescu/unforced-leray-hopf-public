import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.KernelDoubleIntegrable

/-!
# Positive-age heat / divergence covariance for bounded continuous inputs

The actual B0284 Gaussian heat applied to the actual B0296 divergence convolution is the summed-age
B0296 divergence convolution for bounded continuous tensor fields. The proof uses the concrete
product-kernel L¹ estimate, a measure-preserving shear, Fubini, and the fixed-column Gaussian
kernel identity.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory
open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.B0284
open UnforcedLeray.B0289
open UnforcedLeray.B0296
open UnforcedLeray.HeatCylinder

namespace UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

/-- Positive-age actual heat / divergence covariance on a bounded continuous tensor. -/
theorem heat_heatDiv_of_bdd_continuous {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    {T : Plane → Plane × Plane} (hT : Continuous T) {M : ℝ}
    (hTb : ∀ z, ‖T z‖ ≤ M) (z : Plane) :
    ∫ w : Plane, heatKernel2 α w • heatDiv β T (z - w) =
      heatDiv (α + β) T z := by
  let Φ : Plane → Plane → Plane := fun w y =>
    heatKernel2 α w • divKernel β (y - w) (T (z - y))
  have h1 : ∀ w : Plane, heatKernel2 α w • heatDiv β T (z - w) = ∫ y, Φ w y := by
    intro w
    rw [heatDiv_apply_of_pos hβ, ← integral_smul,
      ← integral_sub_right_eq_self
        (fun v : Plane => heatKernel2 α w • divKernel β v (T (z - w - v))) w]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [Φ]
    congr 2
    abel_nf
  have hdouble := integrable_heatDiv_doubleIntegrand hα hβ hT
    (M := M) hTb z
  have hshear : MeasurePreserving (fun p : Plane × Plane => (p.1, p.2 - p.1))
      ((volume : Measure Plane).prod volume) ((volume : Measure Plane).prod volume) :=
    measurePreserving_prod_sub (μ := (volume : Measure Plane))
      (ν := (volume : Measure Plane))
  have hPhi : Integrable (Function.uncurry Φ) ((volume : Measure Plane).prod volume) := by
    have hcomp := hshear.integrable_comp_of_integrable hdouble
    have hEq : Function.uncurry Φ = (fun p : Plane × Plane =>
        heatKernel2 α p.1 • divKernel β (p.2 - p.1) (T (z - p.2))) := by
      funext p
      rfl
    have hcomp' : Integrable (fun p : Plane × Plane =>
        heatKernel2 α p.1 • divKernel β (p.2 - p.1)
          (T (z - p.1 - (p.2 - p.1)))) ((volume : Measure Plane).prod volume) := by
      change Integrable
        ((fun p : Plane × Plane => heatKernel2 α p.1 •
          divKernelCLM β p.2 (T (z - p.1 - p.2))) ∘
          (fun p : Plane × Plane => (p.1, p.2 - p.1))) _
      exact hcomp.congr (Filter.Eventually.of_forall fun p => by
        simp [divKernelCLM_apply])
    have hshift : (fun p : Plane × Plane =>
        heatKernel2 α p.1 • divKernel β (p.2 - p.1)
          (T (z - p.1 - (p.2 - p.1)))) = (fun p =>
        heatKernel2 α p.1 • divKernel β (p.2 - p.1) (T (z - p.2))) := by
      funext p
      congr 2 <;> abel
    have hcomp'' := hcomp'.congr (Filter.Eventually.of_forall fun p => congrFun hshift p)
    exact hcomp''.congr (Filter.Eventually.of_forall fun p => (congrFun hEq p).symm)
  have hSwap := integral_integral_swap hPhi
  calc
    ∫ w : Plane, heatKernel2 α w • heatDiv β T (z - w) =
        ∫ w : Plane, ∫ y : Plane, Φ w y := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall h1
    _ = ∫ y : Plane, ∫ w : Plane, Φ w y := hSwap
    _ = ∫ y : Plane, divKernel (α + β) y (T (z - y)) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
          dsimp [Φ]
          calc
            ∫ w : Plane, heatKernel2 α w • divKernel β (y - w) (T (z - y)) =
                ∫ w : Plane, (fun x : Plane =>
                  heatKernel2 α (y - x) • divKernel β x (T (z - y))) (y - w) := by
                    apply integral_congr_ae
                    filter_upwards [] with w
                    congr 2 <;> abel
            _ = ∫ w : Plane, heatKernel2 α (y - w) •
                  divKernel β w (T (z - y)) :=
              integral_sub_left_eq_self
                (fun x : Plane => heatKernel2 α (y - x) •
                  divKernel β x (T (z - y))) (volume : Measure Plane) y
            _ = divKernel (α + β) y (T (z - y)) :=
              integral_heatKernel2_divKernel_conv hα hβ y (T (z - y))
    _ = heatDiv (α + β) T z := by
          rw [heatDiv_apply_of_pos (add_pos hα hβ)]

end UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

#print axioms UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.heat_heatDiv_of_bdd_continuous
