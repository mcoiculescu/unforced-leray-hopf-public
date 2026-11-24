import UnforcedLeray.Analysis.Pressure.Spatial
import UnforcedLeray.Analysis.Pressure.ParameterIntegral
import UnforcedLeray.Analysis.EnergyInterpolation.Spacetime

/-!
# Actual spacetime integrability of the velocity pressure

The pressure is the literal real Newtonian-gradient potential of the
convective forcing. Joint measurability follows from the parameter-integral
lemma; its spatial norm estimate is integrated with the energy bounds.
-/
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal NNReal
namespace UnforcedLeray.PressureAnalysis

/-- The actual time-dependent Newtonian-gradient potential. -/
def pressureFromVelocity (u : Velocity) (G : FirstDerivatives) : Pressure :=
  fun t => velocityPressure (u t) (G t)

/-- The convective forcing inherits joint measurability from the velocity
and its actual weak derivative fields. -/
theorem velocityForcing_joint_aestronglyMeasurable {μ : Measure SpaceTime}
    {u : Velocity} {G : FirstDerivatives}
    (hu : AEStronglyMeasurable (fun z : SpaceTime => u z.1 z.2) μ)
    (hG : ∀ j, AEStronglyMeasurable (fun z : SpaceTime => G z.1 j z.2) μ)
    (i : Fin 3) :
    AEStronglyMeasurable (fun z : SpaceTime => velocityForcing (u z.1) (G z.1) i z.2) μ := by
  have hterm (j : Fin 3) : AEStronglyMeasurable
      (fun z : SpaceTime => u z.1 z.2 j * G z.1 j z.2 i) μ :=
    ((EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) j).continuous.comp_aestronglyMeasurable hu).mul
      ((EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 3) i).continuous.comp_aestronglyMeasurable (hG j))
  convert ((hterm 0).add (hterm 1)).add (hterm 2) using 1
  funext z
  simp only [velocityForcing, Fin.sum_univ_three, Pi.add_apply]

/-- Measurability is proved for the literal pressure, including its chosen
pointwise representatives; no extra pressure measurability premise occurs. -/
theorem pressureFromVelocity_aestronglyMeasurable {T : ℝ} {u : Velocity} {G : FirstDerivatives}
    (hu : AEStronglyMeasurable (fun z : SpaceTime => u z.1 z.2)
      (volume.restrict (slab T)))
    (hG : ∀ i, AEStronglyMeasurable (fun z : SpaceTime => G z.1 i z.2)
      (volume.restrict (slab T))) :
    AEStronglyMeasurable (fun z : SpaceTime => pressureFromVelocity u G z.1 z.2)
      (volume.restrict (slab T)) := by
  rw [EnergyInterpolation.slab_volume_eq] at hu hG ⊢
  have hterm (i : Fin 3) : AEStronglyMeasurable
      (fun z : SpaceTime => newtonComponent i (velocityForcing (u z.1) (G z.1) i) z.2)
      ((volume.restrict (Ioo (0 : ℝ) T)).prod (volume : Measure Space)) :=
    parameter_convolution_aestronglyMeasurable (newtonGradientKernel_measurable i)
      (velocityForcing_joint_aestronglyMeasurable hu hG i)
  convert ((hterm 0).add (hterm 1)).add (hterm 2) using 1
  all_goals first
    | rfl
    | (funext z; simp only [pressureFromVelocity, velocityPressure, Fin.sum_univ_three, Pi.add_apply])

/-- Identification of the literal scalar power integral with the finite Lᵖ
norm expression used by the spatial estimate. -/
theorem integral_norm_fiveThirds_eq {f : Space → ℝ}
    (hf : AEStronglyMeasurable f volume) :
    (∫ x : Space, ‖f x‖ ^ (5 / 3 : ℝ)) =
      (eLpNorm f (5 / 3 : ℝ≥0∞) volume).toReal ^ (5 / 3 : ℝ) := by
  have ht := integral_toReal (hf.enorm.pow_const (5 / 3 : ℝ))
    (Eventually.of_forall (fun x : Space =>
      ENNReal.rpow_lt_top_of_nonneg (by norm_num : (0 : ℝ) ≤ 5 / 3)
        (enorm_ne_top : ‖f x‖ₑ ≠ ⊤)))
  have he : (∫ x : Space, ‖f x‖ ^ (5 / 3 : ℝ)) =
      (∫⁻ x : Space, ‖f x‖ₑ ^ (5 / 3 : ℝ)).toReal := by
    simpa only [← ENNReal.toReal_rpow, toReal_enorm] using ht
  rw [he]
  have h := eLpNorm_nnreal_pow_eq_lintegral
    (f := f) (μ := volume) (p := (5 / 3 : ℝ≥0)) (by norm_num)
  norm_num only [NNReal.coe_div, NNReal.coe_ofNat, ENNReal.coe_div, ENNReal.coe_ofNat] at h
  rw [← h, ← ENNReal.toReal_rpow]

/-- A fixed concrete constant after replacing the square of the coordinate
norm sum by the genuine gradient dissipation. -/
def pressureEnergyConstant : ℝ := 3 * velocityPressureConstant ^ (5 / 3 : ℝ)

theorem pressureEnergyConstant_nonneg : 0 ≤ pressureEnergyConstant := by
  exact mul_nonneg (by norm_num) (Real.rpow_nonneg velocityPressureConstant_nonneg _)

theorem spatial_pressure_integral_le_uniform {u : SpatialField} {g : Fin 3 → SpatialField} {M : ℝ}
    (hu : MemLp u 2 volume) (hg : ∀ i, MemLp (g i) 2 volume)
    (hweak : ∀ i, HasWeakSpatialDerivative i u (g i))
    (hM0 : 0 ≤ M) (hM : l2Norm u ≤ M) :
    (∫ x : Space, ‖velocityPressure u g x‖ ^ (5 / 3 : ℝ)) ≤
      (pressureEnergyConstant * M ^ (4 / 3 : ℝ)) *
        ∑ i : Fin 3, l2Norm (g i) ^ 2 := by
  rw [integral_norm_fiveThirds_eq (velocityPressure_memLp hu hg hweak).aestronglyMeasurable]
  have hr : l2Norm u ^ (4 / 3 : ℝ) ≤ M ^ (4 / 3 : ℝ) :=
    Real.rpow_le_rpow ENNReal.toReal_nonneg hM (by norm_num)
  calc
    _ ≤ velocityPressureConstant ^ (5 / 3 : ℝ) * l2Norm u ^ (4 / 3 : ℝ) *
        (∑ i : Fin 3, l2Norm (g i)) ^ 2 := velocityPressure_norm_rpow_le hu hg hweak
    _ ≤ velocityPressureConstant ^ (5 / 3 : ℝ) * M ^ (4 / 3 : ℝ) *
        (3 * ∑ i : Fin 3, l2Norm (g i) ^ 2) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hr (Real.rpow_nonneg velocityPressureConstant_nonneg _)
      · exact EnergyInterpolation.coordinate_sum_sq_le g
      · exact sq_nonneg _
      · exact mul_nonneg (Real.rpow_nonneg velocityPressureConstant_nonneg _)
          (Real.rpow_nonneg hM0 _)
    _ = _ := by unfold pressureEnergyConstant; ring

/-- The literal pressure power is integrable on the physical slab. -/
theorem spacetime_pressure_integrable_norm {T M : ℝ} {u : Velocity} {G : FirstDerivatives}
    (hu : AEStronglyMeasurable (fun z : SpaceTime => u z.1 z.2)
      (volume.restrict (slab T)))
    (hG : ∀ i, AEStronglyMeasurable (fun z : SpaceTime => G z.1 i z.2)
      (volume.restrict (slab T)))
    (h2 : ∀ t ∈ Ioo (0 : ℝ) T, MemLp (u t) 2 volume)
    (hg : ∀ t ∈ Ioo (0 : ℝ) T, ∀ i, MemLp (G t i) 2 volume)
    (hweak : ∀ t ∈ Ioo (0 : ℝ) T, ∀ i, HasWeakSpatialDerivative i (u t) (G t i))
    (hM0 : 0 ≤ M) (hM : ∀ t ∈ Ioo (0 : ℝ) T, l2Norm (u t) ≤ M)
    (hD : IntegrableOn (dissipation G) (Ioo (0 : ℝ) T)) :
    Integrable (fun z : SpaceTime => ‖pressureFromVelocity u G z.1 z.2‖ ^ (5 / 3 : ℝ))
      (volume.restrict (slab T)) := by
  have hp := pressureFromVelocity_aestronglyMeasurable hu hG
  rw [EnergyInterpolation.slab_volume_eq] at hp ⊢
  have hpower : AEStronglyMeasurable
      (fun z : SpaceTime => ‖pressureFromVelocity u G z.1 z.2‖ ^ (5 / 3 : ℝ))
      ((volume.restrict (Ioo (0 : ℝ) T)).prod (volume : Measure Space)) :=
    (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 5 / 3)).comp_aestronglyMeasurable hp.norm
  have hint : Integrable
      (fun t => ∫ x : Space, ‖pressureFromVelocity u G t x‖ ^ (5 / 3 : ℝ))
      (volume.restrict (Ioo (0 : ℝ) T)) := by
    apply (hD.const_mul (pressureEnergyConstant * M ^ (4 / 3 : ℝ))).mono'
      hpower.integral_prod_right'
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with t ht
    rw [Real.norm_of_nonneg (integral_nonneg (fun x => Real.rpow_nonneg (norm_nonneg _) _))]
    exact spatial_pressure_integral_le_uniform (h2 t ht) (hg t ht) (hweak t ht) hM0 (hM t ht)
  apply (integrable_prod_iff hpower).mpr
  constructor
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with t ht
    have hm := velocityPressure_memLp (h2 t ht) (hg t ht) (hweak t ht)
    simpa only [ENNReal.toReal_div, ENNReal.toReal_ofNat, pressureFromVelocity] using
      (integrable_norm_rpow_iff hm.aestronglyMeasurable (by norm_num : (5 / 3 : ℝ≥0∞) ≠ 0)
        (by finiteness : (5 / 3 : ℝ≥0∞) ≠ ⊤)).mpr hm
  · simpa only [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)] using hint

/-- Actual L^(5/3) membership, obtained from velocity energy bounds. -/
theorem spacetime_pressure_memLp {T M : ℝ} {u : Velocity} {G : FirstDerivatives}
    (hu : AEStronglyMeasurable (fun z : SpaceTime => u z.1 z.2)
      (volume.restrict (slab T)))
    (hG : ∀ i, AEStronglyMeasurable (fun z : SpaceTime => G z.1 i z.2)
      (volume.restrict (slab T)))
    (h2 : ∀ t ∈ Ioo (0 : ℝ) T, MemLp (u t) 2 volume)
    (hg : ∀ t ∈ Ioo (0 : ℝ) T, ∀ i, MemLp (G t i) 2 volume)
    (hweak : ∀ t ∈ Ioo (0 : ℝ) T, ∀ i, HasWeakSpatialDerivative i (u t) (G t i))
    (hM0 : 0 ≤ M) (hM : ∀ t ∈ Ioo (0 : ℝ) T, l2Norm (u t) ≤ M)
    (hD : IntegrableOn (dissipation G) (Ioo (0 : ℝ) T)) :
    MemLp (fun z : SpaceTime => pressureFromVelocity u G z.1 z.2) (5 / 3 : ℝ≥0∞)
      (volume.restrict (slab T)) := by
  apply (integrable_norm_rpow_iff (pressureFromVelocity_aestronglyMeasurable hu hG)
    (by norm_num : (5 / 3 : ℝ≥0∞) ≠ 0) (by finiteness : (5 / 3 : ℝ≥0∞) ≠ ⊤)).mp
  simpa only [ENNReal.toReal_div, ENNReal.toReal_ofNat] using
    spacetime_pressure_integrable_norm hu hG h2 hg hweak hM0 hM hD

/-- The actual spacetime pressure power is controlled by the integrated
energy dissipation. -/
theorem spacetime_pressure_integral_le {T M : ℝ} {u : Velocity} {G : FirstDerivatives}
    (hu : AEStronglyMeasurable (fun z : SpaceTime => u z.1 z.2)
      (volume.restrict (slab T)))
    (hG : ∀ i, AEStronglyMeasurable (fun z : SpaceTime => G z.1 i z.2)
      (volume.restrict (slab T)))
    (h2 : ∀ t ∈ Ioo (0 : ℝ) T, MemLp (u t) 2 volume)
    (hg : ∀ t ∈ Ioo (0 : ℝ) T, ∀ i, MemLp (G t i) 2 volume)
    (hweak : ∀ t ∈ Ioo (0 : ℝ) T, ∀ i, HasWeakSpatialDerivative i (u t) (G t i))
    (hM0 : 0 ≤ M) (hM : ∀ t ∈ Ioo (0 : ℝ) T, l2Norm (u t) ≤ M)
    (hD : IntegrableOn (dissipation G) (Ioo (0 : ℝ) T)) :
    (∫ z : SpaceTime, ‖pressureFromVelocity u G z.1 z.2‖ ^ (5 / 3 : ℝ)
      ∂volume.restrict (slab T)) ≤
      (pressureEnergyConstant * M ^ (4 / 3 : ℝ)) *
        ∫ t in Ioo (0 : ℝ) T, dissipation G t := by
  have hi := spacetime_pressure_integrable_norm hu hG h2 hg hweak hM0 hM hD
  rw [EnergyInterpolation.slab_volume_eq] at hi ⊢
  rw [integral_prod _ hi]
  calc
    _ ≤ ∫ t in Ioo (0 : ℝ) T,
        (pressureEnergyConstant * M ^ (4 / 3 : ℝ)) * dissipation G t := by
      apply integral_mono_ae hi.integral_prod_left
        (hD.const_mul (pressureEnergyConstant * M ^ (4 / 3 : ℝ)))
      filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with t ht
      exact spatial_pressure_integral_le_uniform (h2 t ht) (hg t ht) (hweak t ht) hM0 (hM t ht)
    _ = _ := integral_const_mul _ _

end UnforcedLeray.PressureAnalysis
