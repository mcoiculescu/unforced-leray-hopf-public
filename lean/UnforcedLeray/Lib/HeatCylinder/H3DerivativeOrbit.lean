import UnforcedLeray.Lib.HeatCylinder.H3OrbitValueContinuity

/-!
# Derivative-indexed Gaussian L² orbits

For a smooth periodic compact-axial tensor, every ordered spatial derivative is again such a
tensor. This leaf exposes the actual positive-age normalized-cell Gaussian orbit for each word,
with its continuity and strong measurability inherited from the concrete kernel result.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.GaussianVortex (Plane)

/-- The normalized-cell vector Gaussian orbit applied to one actual ordered derivative of a
smooth periodic tensor input. -/
noncomputable def heatDivH3DerivativeL2Orbit {c : ℝ} (hc : 0 < c)
    {T : Plane → Plane × Plane} (hT : UnforcedLeray.Sob.IsCylSmooth c T)
    (α : UnforcedLeray.Sob.Idx 2 3) (θ : ℝ) :
    Lp UnforcedLeray.Train.Vec 2 (UnforcedLeray.B0284.cellMeasure c) := by
  let v := (UnforcedLeray.Sob.cylinder c).word α
  let Tα := UnforcedLeray.Sob.iterD v T
  have hTα : UnforcedLeray.Sob.IsCylSmooth c Tα := hT.iterD v
  have hper : UnforcedLeray.B0284.IsQPeriodic c Tα := by
    intro z
    have hcoord : (z.1 + c, z.2) = z + (c, 0) := by ext <;> simp
    rw [hcoord]
    exact hTα.periodic z
  exact heatDivVecL2Orbit hc
    hper hTα.smooth.continuous.measurable
    (memLp_tensor_iterD_cylSmooth_normalized hc hTα []) θ

/-- Every derivative-word normalized-cell Gaussian orbit is strongly continuous at positive
heat age. -/
theorem continuousAt_heatDivH3DerivativeL2Orbit {c θ₀ : ℝ} (hc : 0 < c)
    (hθ₀ : 0 < θ₀) {T : Plane → Plane × Plane}
    (hT : UnforcedLeray.Sob.IsCylSmooth c T)
    (α : UnforcedLeray.Sob.Idx 2 3) :
    ContinuousAt (heatDivH3DerivativeL2Orbit hc hT α) θ₀ := by
  let v := (UnforcedLeray.Sob.cylinder c).word α
  let Tα := UnforcedLeray.Sob.iterD v T
  have hTα : UnforcedLeray.Sob.IsCylSmooth c Tα := hT.iterD v
  have hper : UnforcedLeray.B0284.IsQPeriodic c Tα := by
    intro z
    have hcoord : (z.1 + c, z.2) = z + (c, 0) := by ext <;> simp
    rw [hcoord]
    exact hTα.periodic z
  change ContinuousAt (heatDivVecL2Orbit hc hper hTα.smooth.continuous.measurable
    (memLp_tensor_iterD_cylSmooth_normalized hc hTα []) ) θ₀
  exact continuousAt_heatDivVecL2Orbit hc hθ₀ hper
    hTα.smooth.continuous.measurable
    (memLp_tensor_iterD_cylSmooth_normalized hc hTα [])

end UnforcedLeray.HeatCylinder

#print axioms UnforcedLeray.HeatCylinder.continuousAt_heatDivH3DerivativeL2Orbit

