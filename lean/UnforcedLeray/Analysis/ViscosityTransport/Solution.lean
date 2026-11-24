import UnforcedLeray.Analysis.ViscosityTransport.Equation
import UnforcedLeray.Analysis.ViscosityTransport.Energy
import UnforcedLeray.Analysis.ViscosityTransport.L2Dilation

/-!
# Normalization of a concrete solution with arbitrary positive viscosity

The source class records exactly the regularity, weak derivatives, initial
trace and energy properties in `IsTheoremASolution`, with viscosity made
explicit in the equation and energy identity. A supplied member of this
class is transported to the existing viscosity-one solution class by the
actual spatial dilation. This theorem does not assert existence of a source
solution or of nonunique solutions.
-/

noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal Topology
open UnforcedLeray.SpatialScaling
namespace UnforcedLeray.ViscosityTransport

/-- The full concrete solution class with the viscosity coefficient exposed. -/
structure IsTheoremASolutionViscosity (ν T : ℝ) (u₀ : SpatialField) (u : Velocity)
    (p : Pressure) (G : FirstDerivatives) (H : SecondDerivatives) : Prop where
  velocity_measurable : AEStronglyMeasurable (fun z : SpaceTime => u z.1 z.2)
    (volume.restrict (slab T))
  gradient_measurable : ∀ i, AEStronglyMeasurable (fun z : SpaceTime => G z.1 i z.2)
    (volume.restrict (slab T))
  memL2 : ∀ t ∈ Icc (0 : ℝ) T, MemLp (u t) 2 volume
  solenoidal : ∀ t ∈ Icc (0 : ℝ) T, IsSolenoidal (u t)
  continuousL2 : ContinuousOn (fun t => toL2 (u t)) (Icc (0 : ℝ) T)
  initial_value : u 0 =ᵐ[volume] u₀
  strong_initial_trace : Tendsto (fun t => l2Norm (u t - u₀))
    (𝓝[Icc (0 : ℝ) T] 0) (𝓝 0)
  gradient_memL2 : ∀ t ∈ Ioc (0 : ℝ) T, ∀ i, MemLp (G t i) 2 volume
  second_memL2 : ∀ t ∈ Ioc (0 : ℝ) T, ∀ i j, MemLp (H t i j) 2 volume
  weak_gradient : ∀ t ∈ Ioc (0 : ℝ) T, ∀ i, HasWeakSpatialDerivative i (u t) (G t i)
  weak_second : ∀ t ∈ Ioc (0 : ℝ) T, ∀ i j,
    HasWeakSpatialDerivative j (G t i) (H t i j)
  finite_H1_integral : IntegrableOn (fun t => l2Norm (u t) ^ 2 + dissipation G t)
    (Ioo (0 : ℝ) T)
  finite_dissipation : IntegrableOn (dissipation G) (Ioo (0 : ℝ) T)
  positive_gradient_continuity : ∀ δ, 0 < δ → δ < T → ∀ i,
    ContinuousOn (fun t => toL2 (G t i)) (Icc δ T)
  positive_second_continuity : ∀ δ, 0 < δ → δ < T → ∀ i j,
    ContinuousOn (fun t => toL2 (H t i j)) (Icc δ T)
  pressure_memLp : MemLp (fun z : SpaceTime => p z.1 z.2) (5 / 3 : ℝ≥0∞)
    (volume.restrict (slab T))
  equation : SolvesNavierStokesViscosity ν T u₀ u p
  energy_equality : ∀ t₀ t₁, 0 ≤ t₀ → t₀ ≤ t₁ → t₁ ≤ T →
    (1 / 2 : ℝ) * l2Norm (u t₁) ^ 2 + ν * (∫ t in Ioo t₀ t₁, dissipation G t) =
      (1 / 2 : ℝ) * l2Norm (u t₀) ^ 2


/-- The viscosity-one source class is exactly the solution class in Statement. -/
theorem solution_viscosity_one_iff (T : ℝ) (u₀ : SpatialField) (u : Velocity)
    (p : Pressure) (G : FirstDerivatives) (H : SecondDerivatives) :
    IsTheoremASolutionViscosity 1 T u₀ u p G H ↔ IsTheoremASolution T u₀ u p G H := by
  constructor
  · intro hu
    exact ⟨hu.velocity_measurable, hu.gradient_measurable, hu.memL2, hu.solenoidal,
      hu.continuousL2, hu.initial_value, hu.strong_initial_trace,
      hu.gradient_memL2, hu.second_memL2, hu.weak_gradient, hu.weak_second,
      hu.finite_H1_integral, hu.finite_dissipation, hu.positive_gradient_continuity,
      hu.positive_second_continuity, hu.pressure_memLp,
      (viscosity_one_iff T u₀ u p).mp hu.equation,
      by simpa only [one_mul] using hu.energy_equality⟩
  · intro hu
    exact ⟨hu.velocity_measurable, hu.gradient_measurable, hu.memL2, hu.solenoidal,
      hu.continuousL2, hu.initial_value, hu.strong_initial_trace,
      hu.gradient_memL2, hu.second_memL2, hu.weak_gradient, hu.weak_second,
      hu.finite_H1_integral, hu.finite_dissipation, hu.positive_gradient_continuity,
      hu.positive_second_continuity, hu.pressure_memLp,
      (viscosity_one_iff T u₀ u p).mpr hu.equation,
      by simpa only [one_mul] using hu.energy_equality⟩

/-- Normalization of the full concrete solution, including its actual weak
PDE, finite energy, H1/H2 regularity, pressure class, initial trace, and energy
identity. The time interval is unchanged. -/
theorem normalize_solution {h T : ℝ} (hh : 0 < h) (hT : 0 ≤ T)
    {u₀ : SpatialField} {u : Velocity} {p : Pressure}
    {G : FirstDerivatives} {H : SecondDerivatives}
    (hu : IsTheoremASolutionViscosity h T u₀ u p G H) :
    IsTheoremASolution T (viscosityScale h u₀) (normalizedVelocity h u)
      (scalePressure h⁻¹ (Real.sqrt h) p) (normalizedGradient h G) (normalizedSecond h H) := by
  have hb : Real.sqrt h ≠ 0 := (Real.sqrt_pos.mpr hh).ne'
  have h₀ : MemLp u₀ 2 volume :=
    MemLp.ae_eq hu.initial_value (hu.memL2 0 ⟨le_rfl, hT⟩)
  constructor
  · exact (aestronglyMeasurable_comp_spaceMap hu.velocity_measurable hb).const_smul
      (h ^ (-1 / 2 : ℝ))
  · intro i
    have hi := aestronglyMeasurable_comp_spaceMap (hu.gradient_measurable i) hb
    simpa only [Function.comp_def, spaceMap, normalizedGradient, spatialScale, one_smul] using hi
  · intro t ht
    exact memLp_normalizedVelocity (hu.memL2 t ht) hh
  · intro t ht
    exact solenoidal_normalizedVelocity (hu.solenoidal t ht) hh
  · exact continuousOn_toL2_spatialScale hu.memL2 hu.continuousL2 _ (Real.sqrt_pos.mpr hh)
  · exact initial_value_normalized hu.initial_value hh
  · exact strong_initial_trace_normalized hu.memL2 h₀ hu.strong_initial_trace hh
  · intro t ht i
    exact memLp_normalizedGradient (hu.gradient_memL2 t ht i) hh
  · intro t ht i j
    exact memLp_normalizedSecond (hu.second_memL2 t ht i j) hh
  · intro t ht i
    exact weak_gradient_normalized (hu.weak_gradient t ht i) hh
  · intro t ht i j
    exact weak_second_normalized (hu.weak_second t ht i j) hh
  · exact integrable_H1_normalized u G measurableSet_Ioo
      (fun t ht => hu.memL2 t ⟨ht.1.le, ht.2.le⟩)
      (fun t ht => hu.gradient_memL2 t ⟨ht.1, ht.2.le⟩)
      hu.finite_H1_integral hu.finite_dissipation hh
  · exact integrable_dissipation_normalizedGradient G measurableSet_Ioo
      (fun t ht => hu.gradient_memL2 t ⟨ht.1, ht.2.le⟩) hu.finite_dissipation hh
  · intro δ hδ hδT i
    exact continuousOn_toL2_spatialScale
      (fun t ht => hu.gradient_memL2 t ⟨lt_of_lt_of_le hδ ht.1, ht.2⟩ i)
      (hu.positive_gradient_continuity δ hδ hδT i) _ (Real.sqrt_pos.mpr hh)
  · intro δ hδ hδT i j
    exact continuousOn_toL2_spatialScale
      (fun t ht => hu.second_memL2 t ⟨lt_of_lt_of_le hδ ht.1, ht.2⟩ i j)
      (hu.positive_second_continuity δ hδ hδT i j) _ (Real.sqrt_pos.mpr hh)
  · have hi := (memLp_comp_spaceMap hu.pressure_memLp hb).const_smul h⁻¹
    convert hi using 1
    rfl
  · exact solves_viscosity_normalization hh hu.equation
  · intro t₀ t₁ ht₀ ht₀₁ ht₁
    exact energy_equality_normalized u G t₀ t₁
      (hu.memL2 t₀ ⟨ht₀, le_trans ht₀₁ ht₁⟩)
      (hu.memL2 t₁ ⟨le_trans ht₀ ht₀₁, ht₁⟩)
      (fun t ht => hu.gradient_memL2 t ⟨lt_of_le_of_lt ht₀ ht.1, le_trans ht.2.le ht₁⟩)
      hh (hu.energy_equality t₀ t₁ ht₀ ht₀₁ ht₁)

end UnforcedLeray.ViscosityTransport
