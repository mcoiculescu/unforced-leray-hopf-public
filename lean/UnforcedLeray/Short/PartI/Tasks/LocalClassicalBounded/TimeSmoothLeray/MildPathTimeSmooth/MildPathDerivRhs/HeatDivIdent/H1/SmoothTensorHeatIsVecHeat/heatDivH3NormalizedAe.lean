import UnforcedLeray.Short.PartI.Sub.PartI_T02_1_4_4_1_5_1_1_2

/-!
# `heatDivH3NormalizedAe`: the normalized value of `heatDivH3 S` is a.e. the Gaussian `heatDiv`

Proves `HeatDivH3NormalizedAe` (defined in `PartI_T02_1_4_4_1_5_1_1_2.lean`, source
`the November 2 reference manuscript` lines 3594-3625). Uses
`HeatCylinder.vectorH3NormalizedValue_heatDivH3` (the normalized value is the L² quotient
operator applied to `S`), then `HeatCylinder.heatDivVecL2CLM_apply_to_periodic`, and finally the
coercion of the periodic L² class.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.HeatCylinder

theorem heatDivH3NormalizedAe : HeatDivH3NormalizedAe := by
  intro c θ hc hθ S hS
  have hmem : MemLp S 2 (UnforcedLeray.B0284.cellMeasure c) := by
    simpa only [UnforcedLeray.Sob.iterD_nil] using
      memLp_tensor_iterD_cylSmooth_normalized hc hS []
  have hper : UnforcedLeray.B0284.IsQPeriodic c S := by
    intro z
    have hcoord : (z.1 + c, z.2) = z + (c, 0) := by ext <;> simp
    rw [hcoord]
    exact hS.periodic z
  rw [vectorH3NormalizedValue_heatDivH3 hc hθ hS,
    heatDivVecL2CLM_apply_to_periodic hc hθ hper hS.smooth.continuous.measurable.aestronglyMeasurable
      hmem]
  exact (periodicHeatDivVecMemLp hc hθ S hper
    hS.smooth.continuous.measurable.aestronglyMeasurable hmem).coeFn_toLp

end UnforcedLeray.Short.PartI
