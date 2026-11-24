import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.AxialHeatAgeZero
import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.PhysicalHeatS0

/-!
# Positive-side age-zero continuity of the actual weighted heat

The fixed-cylinder increment estimate and the two actual centered-cell limits yield strong
continuity at zero. The cylinder-dependent weight comparison remains explicit.
-/

set_option autoImplicit false
set_option maxHeartbeats 500000

noncomputable section

open MeasureTheory
open Filter
open Set
open scoped ENNReal Topology
open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.B0579 hiding Plane

namespace UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

/-- Positive-side strong continuity at age zero for the actual weighted Gaussian heat on `X_m`.
The family is totalized by the identity outside `0 < θ ≤ 1`; this is immaterial on the
positive-side filter at zero. -/
theorem tendsto_xColumnHeatS0Positive_apply_zero {c m : ℝ} (hc : 0 < c)
    (hc1 : 1 ≤ c) (hm : 1 ≤ m) (f : X c m) :
    Tendsto (fun θ : ℝ =>
      if hθ : 0 < θ then
        if hθ1 : θ ≤ 1 then xColumnHeatS0Positive hc hm hθ hθ1 f else f
      else f)
      (nhdsWithin (0 : ℝ) (Ioi (0 : ℝ))) (𝓝 f) := by
  let U : ℝ → X c m := fun θ =>
    if hθ : 0 < θ then
      if hθ1 : θ ≤ 1 then xColumnHeatS0Positive hc hm hθ hθ1 f else f
    else f
  have hcomm := tendsto_actualAxialHeatCommutator_centered_norm hc hm f
  have hinc := tendsto_actualAxialHeatIncrement_centered_norm hc hm f
  let Cc : ℝ := (1 + c ^ 2 / 4) ^ (m / 2)
  have hsum : Tendsto (fun θ : ℝ => Cc *
      ((eLpNorm (actualAxialHeatCommutator (θ := θ) hc f) 2
            (Cyl.cellμ c)).toReal +
        (eLpNorm (actualAxialHeatIncrement (θ := θ) hc f) 2
            (Cyl.cellμ c)).toReal))
      (nhdsWithin (0 : ℝ) (Ioi (0 : ℝ))) (𝓝 0) := by
    have hadd := hcomm.add hinc
    have hmul := (tendsto_const_nhds : Tendsto (fun _ : ℝ => Cc)
      (nhdsWithin (0 : ℝ) (Ioi (0 : ℝ))) (𝓝 Cc)).mul hadd
    simpa [Cc] using hmul
  have hlt0 : Iio (1 : ℝ) ∈ 𝓝 (0 : ℝ) :=
    Iio_mem_nhds (by norm_num : (0 : ℝ) < 1)
  have hlt : ∀ᶠ θ : ℝ in nhdsWithin (0 : ℝ) (Ioi 0), θ < 1 := by
    have h : ∀ᶠ θ : ℝ in 𝓝 (0 : ℝ), θ ∈ Iio (1 : ℝ) := hlt0
    filter_upwards [h.filter_mono nhdsWithin_le_nhds] with θ hθ
    exact hθ
  have hdomain : ∀ᶠ θ : ℝ in nhdsWithin (0 : ℝ) (Ioi (0 : ℝ)), 0 < θ ∧ θ ≤ 1 := by
    have hpos : ∀ᶠ θ : ℝ in nhdsWithin (0 : ℝ) (Ioi 0), 0 < θ := by
      have h : ∀ᶠ θ : ℝ in nhdsWithin (0 : ℝ) (Ioi 0), θ ∈ Ioi (0 : ℝ) :=
        self_mem_nhdsWithin
      filter_upwards [h] with θ hθ
      exact hθ
    filter_upwards [hpos, hlt] with θ hθ hθ1
    exact ⟨hθ, le_of_lt hθ1⟩
  have hnorm_nonneg : ∀ᶠ θ : ℝ in nhdsWithin (0 : ℝ) (Ioi (0 : ℝ)),
      0 ≤ ‖U θ - f‖ := by
    filter_upwards [] with θ
    exact norm_nonneg _
  have hnorm_le : ∀ᶠ θ : ℝ in nhdsWithin (0 : ℝ) (Ioi (0 : ℝ)),
      ‖U θ - f‖ ≤ Cc *
        ((eLpNorm (actualAxialHeatCommutator (θ := θ) hc f) 2
              (Cyl.cellμ c)).toReal +
          (eLpNorm (actualAxialHeatIncrement (θ := θ) hc f) 2
              (Cyl.cellμ c)).toReal) := by
    filter_upwards [hdomain] with θ hθ
    dsimp [U]
    simp only [dif_pos hθ.1, dif_pos hθ.2]
    exact norm_xColumnHeatS0Positive_sub_le_centered_terms hc hc1 hm hθ.1 hθ.2 f
  have hnorm : Tendsto (fun θ : ℝ => ‖U θ - f‖)
      (nhdsWithin (0 : ℝ) (Ioi (0 : ℝ))) (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hsum hnorm_nonneg hnorm_le
  have hU : Tendsto U (nhdsWithin (0 : ℝ) (Ioi (0 : ℝ))) (𝓝 f) :=
    tendsto_iff_norm_sub_tendsto_zero.mpr (by simpa using hnorm)
  simpa [U] using hU

end UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

#print axioms UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.tendsto_xColumnHeatS0Positive_apply_zero
