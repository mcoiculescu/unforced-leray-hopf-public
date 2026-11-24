import UnforcedLeray.Analysis.ViscosityTransport.Pairings
import UnforcedLeray.Analysis.ViscosityTransport.MeasureScaling

/-!
# Transport of the actual weak Navier–Stokes equation to viscosity one

Every transformed term is integrable on the actual time slab. The spatial
Jacobian and amplitude multiply both the spacetime integral and the initial
trace by the same constant, giving the zero-force weak equation directly.
The theorem transports a supplied solution; it does not construct one.
-/

noncomputable section
open Set MeasureTheory
open UnforcedLeray.SpatialScaling
namespace UnforcedLeray.ViscosityTransport

/-- The full viscosity-dependent integrand is genuinely integrable. -/
theorem SolvesNavierStokesViscosity.integrand_integrable
    {ν T : ℝ} {u₀ : SpatialField} {u : Velocity} {p : Pressure}
    (h : SolvesNavierStokesViscosity ν T u₀ u p)
    {φ : SpaceTime → Space} (hφ : IsSpacetimeTest T φ) :
    IntegrableOn (viscosityWeakIntegrand ν u p φ) (slab T) :=
  (((h.temporal_integrable φ hφ).add (h.convection_integrable φ hφ)).add
    ((h.diffusion_integrable φ hφ).const_mul ν)).add (h.pressure_integrable φ hφ)

/-- General algebraic form of viscosity normalization. The amplitude and
spatial scale satisfy the exact relations for the concrete pointwise map. -/
theorem solves_spatial_normalization {ν T : ℝ} {u₀ : SpatialField}
    {u : Velocity} {p : Pressure}
    (h : SolvesNavierStokesViscosity ν T u₀ u p)
    (a b c : ℝ) (hb : b ≠ 0) (hab : a * b = 1)
    (hbν : b ^ 2 = ν) (hcb : c * b = a) :
    SolvesUnforcedNavierStokes T (spatialScale a b u₀)
      (scaleVelocity a b u) (scalePressure c b p) := by
  constructor
  · intro φ hφ
    have hi := (integrableOn_comp_spaceMap
      (h.temporal_integrable (pullbackTest b φ) (isSpacetimeTest_pullback hφ hb)) hb).const_mul a
    simpa only [IntegrableOn, Function.comp_def, ← temporalTerm_scale a b hb] using hi
  · intro φ hφ
    have hi := (integrableOn_comp_spaceMap
      (h.convection_integrable (pullbackTest b φ) (isSpacetimeTest_pullback hφ hb)) hb).const_mul (a ^ 2 * b)
    simpa only [IntegrableOn, Function.comp_def, ← convectionTerm_scale a b hb] using hi
  · intro φ hφ
    have hi := (integrableOn_comp_spaceMap
      (h.diffusion_integrable (pullbackTest b φ) (isSpacetimeTest_pullback hφ hb)) hb).const_mul (a * b ^ 2)
    simpa only [IntegrableOn, Function.comp_def, ← diffusionTerm_scale a b hb] using hi
  · intro φ hφ
    have hi := (integrableOn_comp_spaceMap
      (h.pressure_integrable (pullbackTest b φ) (isSpacetimeTest_pullback hφ hb)) hb).const_mul (c * b)
    simpa only [IntegrableOn, Function.comp_def, ← pressureTerm_scale c b hb] using hi
  · intro φ hφ
    have hi := ((h.datum_integrable (pullbackTest b φ)
      (isSpacetimeTest_pullback hφ hb)).comp_smul hb).const_mul a
    simpa only [← datumPairing_scale a b hb] using hi
  · intro φ hφ
    have hψ := isSpacetimeTest_pullback hφ hb
    have hi := h.integrand_integrable hψ
    have hd : (∫ x : Space, inner ℝ (u₀ (b • x)) (pullbackTest b φ (0, b • x))) =
        |(b ^ 3)⁻¹| * (∫ x : Space, inner ℝ (u₀ x) (pullbackTest b φ (0, x))) := by
      simpa [Space, finrank_euclideanSpace, smul_eq_mul] using
        Measure.integral_comp_smul (volume : Measure Space)
          (fun x => inner ℝ (u₀ x) (pullbackTest b φ (0, x))) b
    simp_rw [weakIntegrand_scale a b c ν hb hab hbν hcb,
      datumPairing_scale a b hb, integral_const_mul]
    rw [iterated_integral_comp_spaceMap _ T b hi hb, hd]
    calc
      _ = (a * |(b ^ 3)⁻¹|) *
          ((∫ t in Ioo (0 : ℝ) T, ∫ x : Space,
            viscosityWeakIntegrand ν u p (pullbackTest b φ) (t, x)) +
            (∫ x : Space, inner ℝ (u₀ x) (pullbackTest b φ (0, x)))) := by ring
      _ = 0 := by rw [h.identity (pullbackTest b φ) hψ, mul_zero]

/-- The exact transform in manuscript §2: positive viscosity h becomes one,
with velocity amplitude h^(-1/2), coordinate scale sqrt h, and pressure h⁻¹.
The conclusion includes integrability of all pairings and the initial term. -/
theorem solves_viscosity_normalization {h T : ℝ} (hh : 0 < h)
    {u₀ : SpatialField} {u : Velocity} {p : Pressure}
    (hu : SolvesNavierStokesViscosity h T u₀ u p) :
    SolvesUnforcedNavierStokes T (viscosityScale h u₀)
      (scaleVelocity (h ^ (-1 / 2 : ℝ)) (Real.sqrt h) u)
      (scalePressure h⁻¹ (Real.sqrt h) p) :=
  solves_spatial_normalization hu _ _ _ (Real.sqrt_pos.mpr hh).ne'
    (DerivativeScaling.viscosity_first_amplitude hh) (Real.sq_sqrt hh.le)
    (viscosity_pressure_amplitude hh)

end UnforcedLeray.ViscosityTransport
