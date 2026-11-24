import UnforcedLeray.Units.B0289.Semigroup
import UnforcedLeray.Units.B0296.Kernel
import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.KernelDerivativeConvolution

/-!
# Planar Gaussian-gradient convolution

The planar response kernel factors into its two one-dimensional coordinates. This lifts the
checked scalar derivative convolution to both components of the actual B0296 gradient kernel.
-/

set_option autoImplicit false
set_option maxHeartbeats 500000

noncomputable section

open MeasureTheory
open Filter
open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.B0284
open UnforcedLeray.B0289
open UnforcedLeray.B0296

namespace UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

/-- The first component of the planar gradient kernel obeys the summed-age convolution law. -/
theorem integral_heatKernel2_gradHeatKernel2_conv_fst {α β : ℝ} (hα : 0 < α)
    (hβ : 0 < β) (z : Plane) :
    ∫ w : Plane, heatKernel2 α (z - w) * (gradHeatKernel2 β w).1 =
      (gradHeatKernel2 (α + β) z).1 := by
  let fq : ℝ → ℝ := fun x => B0191.heatKernel 1 α (z.1 - x) * dHeatKernel β x
  let fη : ℝ → ℝ := fun x => B0191.heatKernel 1 α (z.2 - x) * B0191.heatKernel 1 β x
  have hfactor (w : Plane) : heatKernel2 α (z - w) * (gradHeatKernel2 β w).1 =
      fq w.1 * fη w.2 := by
    simp [fq, fη, heatKernel2, gradHeatKernel2, Prod.fst_sub, Prod.snd_sub]
    ring
  calc
    ∫ w : Plane, heatKernel2 α (z - w) * (gradHeatKernel2 β w).1 =
        ∫ w : Plane, fq w.1 * fη w.2 := by
          apply integral_congr_ae
          exact Eventually.of_forall hfactor
    _ = (∫ x : ℝ, fq x) * ∫ x : ℝ, fη x := by
          rw [show (∫ w : Plane, fq w.1 * fη w.2) =
              ∫ w : Plane, fq w.1 * fη w.2 ∂((volume : Measure ℝ).prod volume) by rfl]
          exact integral_prod_mul fq fη
    _ = (gradHeatKernel2 (α + β) z).1 := by
          simp only [fq, fη, integral_heatKernel1_dHeatKernel_conv hα hβ,
            integral_heatKernel1_conv hα hβ, gradHeatKernel2]

/-- The second component of the planar gradient kernel obeys the summed-age convolution law. -/
theorem integral_heatKernel2_gradHeatKernel2_conv_snd {α β : ℝ} (hα : 0 < α)
    (hβ : 0 < β) (z : Plane) :
    ∫ w : Plane, heatKernel2 α (z - w) * (gradHeatKernel2 β w).2 =
      (gradHeatKernel2 (α + β) z).2 := by
  let fq : ℝ → ℝ := fun x => B0191.heatKernel 1 α (z.1 - x) * B0191.heatKernel 1 β x
  let fη : ℝ → ℝ := fun x => B0191.heatKernel 1 α (z.2 - x) * dHeatKernel β x
  have hfactor (w : Plane) : heatKernel2 α (z - w) * (gradHeatKernel2 β w).2 =
      fq w.1 * fη w.2 := by
    simp [fq, fη, heatKernel2, gradHeatKernel2, Prod.fst_sub, Prod.snd_sub]
    ring
  calc
    ∫ w : Plane, heatKernel2 α (z - w) * (gradHeatKernel2 β w).2 =
        ∫ w : Plane, fq w.1 * fη w.2 := by
          apply integral_congr_ae
          exact Eventually.of_forall hfactor
    _ = (∫ x : ℝ, fq x) * ∫ x : ℝ, fη x := by
          rw [show (∫ w : Plane, fq w.1 * fη w.2) =
              ∫ w : Plane, fq w.1 * fη w.2 ∂((volume : Measure ℝ).prod volume) by rfl]
          exact integral_prod_mul fq fη
    _ = (gradHeatKernel2 (α + β) z).2 := by
          simp only [fq, fη, integral_heatKernel1_conv hα hβ,
            integral_heatKernel1_dHeatKernel_conv hα hβ, gradHeatKernel2]

/-- Componentwise form of planar gradient-kernel convolution. -/
theorem integral_heatKernel2_gradHeatKernel2_conv {α β : ℝ} (hα : 0 < α)
    (hβ : 0 < β) (z : Plane) :
    (∫ w : Plane, heatKernel2 α (z - w) * (gradHeatKernel2 β w).1,
      ∫ w : Plane, heatKernel2 α (z - w) * (gradHeatKernel2 β w).2) =
      gradHeatKernel2 (α + β) z := by
  exact Prod.ext (integral_heatKernel2_gradHeatKernel2_conv_fst hα hβ z)
    (integral_heatKernel2_gradHeatKernel2_conv_snd hα hβ z)

end UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

#print axioms UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.integral_heatKernel2_gradHeatKernel2_conv
