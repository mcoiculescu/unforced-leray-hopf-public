import UnforcedLeray.Analysis.EnergyInterpolation.Spatial
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Genuine spacetime L^(10/3) from the energy bounds

The actual spatial Sobolev/interpolation inequality is integrated on the
ordinary product of time and Euclidean R³. Joint measurability, finite
spatial Lᵖ membership, and Fubini's integrability conditions are all retained.
No pressure estimate or Riesz-transform boundedness is asserted here.
-/
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal
namespace UnforcedLeray.EnergyInterpolation

/-- The fixed constant after comparing the coordinate norm sum to dissipation. -/
def energyInterpolationConstant : ℝ := 3 * (SobolevEmbedding.sobolevConstant : ℝ) ^ 2

theorem energyInterpolationConstant_nonneg : 0 ≤ energyInterpolationConstant := by
  unfold energyInterpolationConstant
  positivity

/-- The coordinate-sum norm in the homogeneous Sobolev estimate is controlled
by the actual square-sum dissipation. -/
theorem coordinate_sum_sq_le (g : Fin 3 → SpatialField) :
    (∑ i : Fin 3, l2Norm (g i)) ^ 2 ≤ 3 * ∑ i : Fin 3, l2Norm (g i) ^ 2 := by
  rw [Fin.sum_univ_three, Fin.sum_univ_three]
  nlinarith [sq_nonneg (l2Norm (g 0) - l2Norm (g 1)),
    sq_nonneg (l2Norm (g 1) - l2Norm (g 2)),
    sq_nonneg (l2Norm (g 2) - l2Norm (g 0))]

/-- Exact identification of the restricted spacetime measure with time-space product. -/
theorem slab_volume_eq (T : ℝ) :
    (volume : Measure SpaceTime).restrict (slab T) =
      (volume.restrict (Ioo (0 : ℝ) T)).prod (volume : Measure Space) := by
  exact (Measure.restrict_prod_eq_prod_univ
    (μ := (volume : Measure ℝ)) (ν := (volume : Measure Space)) (Ioo (0 : ℝ) T)).symm

/-- A uniform L² bound turns the spatial interpolation inequality into a
constant multiple of the genuine dissipation density. -/
theorem spatial_integral_le_uniform {f : SpatialField} {g : Fin 3 → SpatialField} {M : ℝ}
    (hf : MemLp f 2 volume) (hg : ∀ i, MemLp (g i) 2 volume)
    (hweak : ∀ i, HasWeakSpatialDerivative i f (g i))
    (hM0 : 0 ≤ M) (hM : l2Norm f ≤ M) :
    (∫ x : Space, ‖f x‖ ^ (10 / 3 : ℝ)) ≤
      (energyInterpolationConstant * M ^ (4 / 3 : ℝ)) *
        ∑ i : Fin 3, l2Norm (g i) ^ 2 := by
  have hr : l2Norm f ^ (4 / 3 : ℝ) ≤ M ^ (4 / 3 : ℝ) :=
    Real.rpow_le_rpow ENNReal.toReal_nonneg hM (by norm_num)
  calc
    _ ≤ (SobolevEmbedding.sobolevConstant : ℝ) ^ 2 *
        l2Norm f ^ (4 / 3 : ℝ) * (∑ i : Fin 3, l2Norm (g i)) ^ 2 :=
      integral_norm_ten_thirds_le hf hg hweak
    _ ≤ (SobolevEmbedding.sobolevConstant : ℝ) ^ 2 *
        M ^ (4 / 3 : ℝ) * (3 * ∑ i : Fin 3, l2Norm (g i) ^ 2) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hr (sq_nonneg _)
      · exact coordinate_sum_sq_le g
      · exact sq_nonneg _
      · exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hM0 _)
    _ = _ := by unfold energyInterpolationConstant; ring

/-- Energy-space assumptions imply integrability of the actual spacetime
10/3-power. Fubini is applied only after establishing finite slice integrals. -/
theorem spacetime_integrable_norm_ten_thirds {T M : ℝ} {u : Velocity} {G : FirstDerivatives}
    (hmeas : AEStronglyMeasurable (fun z : SpaceTime => u z.1 z.2)
      (volume.restrict (slab T)))
    (h2 : ∀ t ∈ Ioo (0 : ℝ) T, MemLp (u t) 2 volume)
    (hg : ∀ t ∈ Ioo (0 : ℝ) T, ∀ i, MemLp (G t i) 2 volume)
    (hweak : ∀ t ∈ Ioo (0 : ℝ) T, ∀ i, HasWeakSpatialDerivative i (u t) (G t i))
    (hM0 : 0 ≤ M) (hM : ∀ t ∈ Ioo (0 : ℝ) T, l2Norm (u t) ≤ M)
    (hD : IntegrableOn (dissipation G) (Ioo (0 : ℝ) T)) :
    Integrable (fun z : SpaceTime => ‖u z.1 z.2‖ ^ (10 / 3 : ℝ))
      (volume.restrict (slab T)) := by
  rw [slab_volume_eq] at hmeas ⊢
  have hpower : AEStronglyMeasurable
      (fun z : SpaceTime => ‖u z.1 z.2‖ ^ (10 / 3 : ℝ))
      ((volume.restrict (Ioo (0 : ℝ) T)).prod (volume : Measure Space)) :=
    (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 10 / 3)).comp_aestronglyMeasurable
      hmeas.norm
  have hint : Integrable (fun t => ∫ x : Space, ‖u t x‖ ^ (10 / 3 : ℝ))
      (volume.restrict (Ioo (0 : ℝ) T)) := by
    apply (hD.const_mul (energyInterpolationConstant * M ^ (4 / 3 : ℝ))).mono'
      hpower.integral_prod_right'
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with t ht
    rw [Real.norm_of_nonneg (integral_nonneg (fun x => Real.rpow_nonneg (norm_nonneg _) _))]
    exact spatial_integral_le_uniform (h2 t ht) (hg t ht) (hweak t ht) hM0 (hM t ht)
  apply (integrable_prod_iff hpower).mpr
  constructor
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with t ht
    exact integrable_norm_ten_thirds (h2 t ht) (hg t ht) (hweak t ht)
  · simpa only [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)] using hint

/-- Genuine L^(10/3) membership on the physical spacetime slab. -/
theorem spacetime_memLp_ten_thirds {T M : ℝ} {u : Velocity} {G : FirstDerivatives}
    (hmeas : AEStronglyMeasurable (fun z : SpaceTime => u z.1 z.2)
      (volume.restrict (slab T)))
    (h2 : ∀ t ∈ Ioo (0 : ℝ) T, MemLp (u t) 2 volume)
    (hg : ∀ t ∈ Ioo (0 : ℝ) T, ∀ i, MemLp (G t i) 2 volume)
    (hweak : ∀ t ∈ Ioo (0 : ℝ) T, ∀ i, HasWeakSpatialDerivative i (u t) (G t i))
    (hM0 : 0 ≤ M) (hM : ∀ t ∈ Ioo (0 : ℝ) T, l2Norm (u t) ≤ M)
    (hD : IntegrableOn (dissipation G) (Ioo (0 : ℝ) T)) :
    MemLp (fun z : SpaceTime => u z.1 z.2) (10 / 3 : ℝ≥0∞)
      (volume.restrict (slab T)) := by
  apply (integrable_norm_rpow_iff hmeas (by norm_num : (10 / 3 : ℝ≥0∞) ≠ 0)
    (by finiteness : (10 / 3 : ℝ≥0∞) ≠ ⊤)).mp
  simpa only [ENNReal.toReal_div, ENNReal.toReal_ofNat] using
    spacetime_integrable_norm_ten_thirds hmeas h2 hg hweak hM0 hM hD

/-- The spacetime 10/3-power is bounded by the actual energy-scale quantity. -/
theorem spacetime_integral_norm_ten_thirds_le {T M : ℝ} {u : Velocity} {G : FirstDerivatives}
    (hmeas : AEStronglyMeasurable (fun z : SpaceTime => u z.1 z.2)
      (volume.restrict (slab T)))
    (h2 : ∀ t ∈ Ioo (0 : ℝ) T, MemLp (u t) 2 volume)
    (hg : ∀ t ∈ Ioo (0 : ℝ) T, ∀ i, MemLp (G t i) 2 volume)
    (hweak : ∀ t ∈ Ioo (0 : ℝ) T, ∀ i, HasWeakSpatialDerivative i (u t) (G t i))
    (hM0 : 0 ≤ M) (hM : ∀ t ∈ Ioo (0 : ℝ) T, l2Norm (u t) ≤ M)
    (hD : IntegrableOn (dissipation G) (Ioo (0 : ℝ) T)) :
    (∫ z : SpaceTime, ‖u z.1 z.2‖ ^ (10 / 3 : ℝ) ∂volume.restrict (slab T)) ≤
      (energyInterpolationConstant * M ^ (4 / 3 : ℝ)) *
        ∫ t in Ioo (0 : ℝ) T, dissipation G t := by
  have hi := spacetime_integrable_norm_ten_thirds hmeas h2 hg hweak hM0 hM hD
  rw [slab_volume_eq] at hi ⊢
  rw [integral_prod _ hi]
  calc
    _ ≤ ∫ t in Ioo (0 : ℝ) T,
        (energyInterpolationConstant * M ^ (4 / 3 : ℝ)) * dissipation G t := by
      apply integral_mono_ae hi.integral_prod_left
        (hD.const_mul (energyInterpolationConstant * M ^ (4 / 3 : ℝ)))
      filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with t ht
      exact spatial_integral_le_uniform (h2 t ht) (hg t ht) (hweak t ht) hM0 (hM t ht)
    _ = _ := integral_const_mul _ _

end UnforcedLeray.EnergyInterpolation
