import UnforcedLeray.Lib.HeatCylinder.KernelOrbitContinuity
import UnforcedLeray.Lib.HeatCylinder.H3Operator
import UnforcedLeray.Lib.HeatCylinder.H3ActualLimit
import UnforcedLeray.Lib.HeatCylinder.VectorL2

/-!
# Continuity of the actual rough H³ heat-divergence value orbit

The order-zero centered Sobolev value of the actual rough H³ Gaussian output is the vectorized
normalized-cell L² orbit. This proves continuity of that actual value at positive heat age.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.B0284 (cellMeasure IsQPeriodic)
open UnforcedLeray.GaussianVortex (Plane)

/-- Train-vector version of the actual normalized-cell L² heat orbit. -/
noncomputable def heatDivVecL2Orbit {c : ℝ} (hc : 0 < c)
    {T : Plane → Plane × Plane} (hper : IsQPeriodic c T)
    (hmeas : Measurable T) (hmem : MemLp T 2 (cellMeasure c)) (θ : ℝ) :
    Lp UnforcedLeray.Train.Vec 2 (cellMeasure c) :=
  ((UnforcedLeray.Train.toVecL : Plane →L[ℝ] UnforcedLeray.Train.Vec).compLpL
    2 (cellMeasure c)) (heatDivL2Orbit hc hper hmeas hmem θ)

/-- The actual normalized-cell vector heat-divergence orbit is strongly continuous at positive
heat ages. -/
theorem continuousAt_heatDivVecL2Orbit {c θ₀ : ℝ} (hc : 0 < c) (hθ₀ : 0 < θ₀)
    {T : Plane → Plane × Plane} (hper : IsQPeriodic c T) (hmeas : Measurable T)
    (hmem : MemLp T 2 (cellMeasure c)) :
    ContinuousAt (heatDivVecL2Orbit hc hper hmeas hmem) θ₀ := by
  exact (((UnforcedLeray.Train.toVecL : Plane →L[ℝ] UnforcedLeray.Train.Vec).compLpL
      2 (cellMeasure c)).continuous.continuousAt.comp
        (continuousAt_heatDivL2Orbit hc hθ₀ hper hmeas hmem))

/-- Total-age representative of the centered value of the actual rough H³ heat-divergence
output, equal to zero for nonpositive ages as in `B0296.heatDiv`. -/
noncomputable def actualHeatDivH3ValueOrbit {c : ℝ} (hc : 0 < c)
    (x : UnforcedLeray.TrainB.TensorH3 c) (θ : ℝ) :
    Lp UnforcedLeray.Train.Vec 2 (cellMeasure c) :=
  if hθ : 0 < θ then
    vectorH3NormalizedValue hc (actualHeatDivH3 hc hθ x)
  else 0

/-- At positive ages, the actual rough H³ output value is precisely the normalized-cell vector
heat-divergence orbit of its actual periodic tensor representative. -/
theorem actualHeatDivH3ValueOrbit_eq {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    (x : UnforcedLeray.TrainB.TensorH3 c) :
    actualHeatDivH3ValueOrbit hc x θ =
      heatDivVecL2Orbit hc (periodic_tensorH3KernelRep hc x)
        (measurable_tensorH3KernelRep hc x)
        (memLp_tensorH3KernelRep_normalized hc x) θ := by
  rw [actualHeatDivH3ValueOrbit, dif_pos hθ,
    vectorH3NormalizedValue_actualHeatDivH3 hc hθ]
  change heatDivVecL2CLM hc hθ (tensorH3KernelInput hc x) = _
  rw [heatDivVecL2CLM_apply]
  change ((UnforcedLeray.Train.toVecL : Plane →L[ℝ] UnforcedLeray.Train.Vec).compLpL
      2 (cellMeasure c))
      (heatDivL2CLM hc hθ
        ((memLp_tensorH3KernelRep_normalized hc x).toLp (tensorH3KernelRep hc x))) =
      ((UnforcedLeray.Train.toVecL : Plane →L[ℝ] UnforcedLeray.Train.Vec).compLpL
        2 (cellMeasure c))
        (heatDivL2Orbit hc (periodic_tensorH3KernelRep hc x)
          (measurable_tensorH3KernelRep hc x)
          (memLp_tensorH3KernelRep_normalized hc x) θ)
  rw [heatDivL2Orbit_eq_CLM hc hθ
    (periodic_tensorH3KernelRep hc x) (measurable_tensorH3KernelRep hc x)
    (memLp_tensorH3KernelRep_normalized hc x)]

/-- The actual rough H³ heat-divergence output has a strongly continuous centered value orbit
on every positive heat-age interval. -/
theorem continuousAt_actualHeatDivH3ValueOrbit {c θ₀ : ℝ} (hc : 0 < c) (hθ₀ : 0 < θ₀)
    (x : UnforcedLeray.TrainB.TensorH3 c) :
    ContinuousAt (actualHeatDivH3ValueOrbit hc x) θ₀ := by
  have hEq : actualHeatDivH3ValueOrbit hc x =ᶠ[𝓝 θ₀]
      heatDivVecL2Orbit hc (periodic_tensorH3KernelRep hc x)
        (measurable_tensorH3KernelRep hc x)
        (memLp_tensorH3KernelRep_normalized hc x) := by
    filter_upwards [Ioi_mem_nhds hθ₀] with θ hθ
    exact actualHeatDivH3ValueOrbit_eq hc hθ x
  exact (continuousAt_heatDivVecL2Orbit hc hθ₀
    (periodic_tensorH3KernelRep hc x) (measurable_tensorH3KernelRep hc x)
    (memLp_tensorH3KernelRep_normalized hc x)).congr_of_eventuallyEq hEq

end UnforcedLeray.HeatCylinder

#print axioms UnforcedLeray.HeatCylinder.continuousAt_actualHeatDivH3ValueOrbit
