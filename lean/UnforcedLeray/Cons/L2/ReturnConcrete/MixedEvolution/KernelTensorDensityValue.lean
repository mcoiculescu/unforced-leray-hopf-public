import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.KernelTensorDensity

/-!
# L² value continuity for the retained tensor smooth-density sequence

The zeroth-order value projection is contractive in the cylinder graph norm. This packages the
continuity step from the existing Sobolev smooth-density sequence to the corresponding L² values.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.TrainB (TensorVal)

/-- Convergence in the order-zero tensor cylinder graph implies convergence of its actual L²
value classes. -/
theorem tendsto_tensorW0_value_of_tendsto {c : ℝ} {y : ℕ → TensorW0 c}
    {x : TensorW0 c} (hy : Tendsto y atTop (𝓝 x)) :
    Tendsto (fun n => UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
      (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ TensorVal 0 2 (y n)) atTop
      (𝓝 (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ TensorVal 0 2 x)) := by
  exact ((UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder c)
    (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ TensorVal 0 2).continuous.tendsto x).comp hy

end UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

#print axioms UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.tendsto_tensorW0_value_of_tendsto
