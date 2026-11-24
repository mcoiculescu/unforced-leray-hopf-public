import UnforcedLeray.Cons.L2.BackgroundConcrete.SpatialProductDerivativeMeas
import UnforcedLeray.Cons.L2.BackgroundConcrete.SpatialProductIBP

/-! Compact spacetime integrability estimates for the actual scalar product and derivative. -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff ENNReal

namespace UnforcedLeray.Cons.C03.Concrete

/-- A continuous compactly supported real multiplier times an a.e. measurable locally bounded
complex field is integrable. -/
theorem integrable_smul_aesm_of_compactMultiplier_bound
    {w : SpaceTime → ℝ} (hw : Continuous w) (hwc : HasCompactSupport w)
    {f : SpaceTime → ℂ} (hf : AEStronglyMeasurable f volume)
    {C : ℝ}
    (hbound : ∀ z ∈ tsupport w, ‖f z‖ ≤ C) :
    Integrable (fun z : SpaceTime => w z • f z) volume := by
  obtain ⟨D, hD⟩ := hw.bounded_above_of_compact_support hwc
  have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD 0)
  let K : Set SpaceTime := tsupport w
  have hK : IsCompact K := hwc
  have hdom : Integrable (K.indicator (fun _ : SpaceTime => D * C)) volume := by
    have hfinite : volume K < (⊤ : ℝ≥0∞) := hK.measure_lt_top
    exact (integrableOn_const (C := D * C) hfinite.ne).integrable_indicator hK.measurableSet
  have hprod : AEStronglyMeasurable (fun z : SpaceTime => w z • f z) volume :=
    hw.aestronglyMeasurable.smul hf
  refine hdom.mono' hprod (Eventually.of_forall fun z => ?_)
  by_cases hz : z ∈ K
  · simp only [Set.indicator_of_mem hz]
    calc
      ‖w z • f z‖ = ‖w z‖ * ‖f z‖ := norm_smul _ _
      _ ≤ D * C := mul_le_mul (hD z) (hbound z hz) (norm_nonneg _) hD0
  · have hw0 : w z = 0 := image_eq_zero_of_notMem_tsupport hz
    simp [hz, hw0]

#print axioms integrable_smul_aesm_of_compactMultiplier_bound

end UnforcedLeray.Cons.C03.Concrete
