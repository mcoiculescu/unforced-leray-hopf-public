import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.AxialHeatCommutator

/-!
# Almost-everywhere finiteness and the actual commutator identity

The finite Gaussian integrals used in the pointwise commutator formula hold almost everywhere
for every actual weighted input column. This removes those finiteness conditions from the useful
cellwise identity.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.B0579 hiding Plane

private theorem ae_heatAbs_lt_top_of_periodic_L2 {c θ : ℝ} (hc : 0 < c)
    (hθ : 0 < θ) {g : Plane → Plane} (hper : B0284.IsQPeriodic c g)
    (hg : AEStronglyMeasurable g volume) (hmem : MemLp g 2 (B0284.cellMeasure c)) :
    ∀ᵐ z ∂(B0284.cellMeasure c), B0284.heatAbs θ g z < ⊤ := by
  let k : Plane → ℝ≥0∞ := fun w => ENNReal.ofReal (B0284.heatKernel2 θ w)
  have hk : Measurable k := ENNReal.measurable_ofReal.comp
    (B0284.measurable_heatKernel2_right θ)
  have hkn : ∀ w, k w ≠ ⊤ := fun w => ENNReal.ofReal_ne_top
  have hmass : ∫⁻ w : Plane, k w = 1 := by
    dsimp [k]
    exact B0284.lintegral_heatKernel2 hθ
  have hkernel := B0296.ae_kernelAbs_lt_top' hc hk hkn
    (by rw [hmass]; exact ENNReal.one_ne_top) hper hg
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) ENNReal.ofNat_ne_top hmem.eLpNorm_ne_top
  simpa [B0284.heatAbs, k] using hkernel

/-- The literal weighted heat commutator identity holds on almost every point of the actual
normalized periodic cell for every real `X_m` input. -/
theorem axialHeatCommutator_ae {c m θ : ℝ} (hc : 0 < c) (hm : 1 ≤ m)
    (hθ : 0 < θ) (f : X c m) :
    ∀ᵐ z ∂(B0284.cellMeasure c),
      axialWeight m z • B0284.heat θ (xColumnHeatLift hc f) z -
        B0284.heat θ (fun x => axialWeight m x • xColumnHeatLift hc f x) z =
        ∫ w : Plane, B0284.heatKernel2 θ w •
          ((axialWeight m z - axialWeight m (z - w)) • xColumnHeatLift hc f (z - w)) := by
  have hRawMem := memLp_xColumnHeatLift_normalized hc hm f
  have hRawMeas : AEStronglyMeasurable (xColumnHeatLift hc f) volume :=
    (stronglyMeasurable_xColumnHeatLift hc f).aestronglyMeasurable
  have hRawPer : B0284.IsQPeriodic c (xColumnHeatLift hc f) :=
    periodic_xColumnHeatLift hc f
  have hAxMeas : AEStronglyMeasurable
      (fun z => axialWeight m z • xColumnHeatLift hc f z) volume :=
    (continuous_axialWeight m).aestronglyMeasurable.smul hRawMeas
  have hAxPer : B0284.IsQPeriodic c
      (fun z => axialWeight m z • xColumnHeatLift hc f z) := by
    intro z
    change axialWeight m (z.1 + c, z.2) • xColumnHeatLift hc f (z.1 + c, z.2) =
      axialWeight m z • xColumnHeatLift hc f z
    rw [show axialWeight m (z.1 + c, z.2) = axialWeight m z by
      simp [axialWeight, axialBracket], periodic_xColumnHeatLift hc f z]
  have hAxMem := HeatCylinder.memLp_cellMeasure_of_memLp_cyl hc
    ((continuous_axialWeight m).measurable.smul
      ((stronglyMeasurable_xColumnHeatLift hc f).measurable)) hAxPer
    (memLp_axialHeatLift_cyl hc hm f)
  have hRawFinite := ae_heatAbs_lt_top_of_periodic_L2 hc hθ hRawPer hRawMeas hRawMem
  have hAxFinite := ae_heatAbs_lt_top_of_periodic_L2 hc hθ hAxPer hAxMeas hAxMem
  filter_upwards [hRawFinite, hAxFinite] with z hzRaw hzAx
  exact axialHeatCommutator_identity hc hm hθ f (z := z)
    (ne_of_lt hzRaw) (ne_of_lt hzAx)

#print axioms UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.axialHeatCommutator_ae

end UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution
