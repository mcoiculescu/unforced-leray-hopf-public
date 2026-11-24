import UnforcedLeray.Statement

/-!
# Concrete viscosity-dependent weak equations and spatial normalization

These are the same zero-force distributional pairings and convergence conditions
as `SolvesUnforcedNavierStokes`, with an explicit coefficient on diffusion.
No existence or transport property is postulated by these definitions.
-/

noncomputable section

open Set MeasureTheory

namespace UnforcedLeray.ViscosityTransport

def spaceMap (b : ℝ) (z : SpaceTime) : SpaceTime := (z.1, b • z.2)

def pullbackTest (b : ℝ) (φ : SpaceTime → Space) (z : SpaceTime) : Space :=
  φ (z.1, b⁻¹ • z.2)

def scaleVelocity (a b : ℝ) (u : Velocity) : Velocity :=
  fun t x => a • u t (b • x)

def scalePressure (c b : ℝ) (p : Pressure) : Pressure :=
  fun t x => c * p t (b • x)

def viscosityWeakIntegrand (ν : ℝ) (u : Velocity) (p : Pressure)
    (φ : SpaceTime → Space) (z : SpaceTime) : ℝ :=
  temporalTerm u φ z + convectionTerm u φ z +
    ν * diffusionTerm u φ z + pressureTerm p φ z

/-- The concrete zero-force weak momentum equation with viscosity `ν`,
including the trace term at time zero and convergence of each pairing. -/
structure SolvesNavierStokesViscosity (ν T : ℝ) (u₀ : SpatialField)
    (u : Velocity) (p : Pressure) : Prop where
  temporal_integrable : ∀ φ, IsSpacetimeTest T φ → IntegrableOn (temporalTerm u φ) (slab T)
  convection_integrable : ∀ φ, IsSpacetimeTest T φ → IntegrableOn (convectionTerm u φ) (slab T)
  diffusion_integrable : ∀ φ, IsSpacetimeTest T φ → IntegrableOn (diffusionTerm u φ) (slab T)
  pressure_integrable : ∀ φ, IsSpacetimeTest T φ → IntegrableOn (pressureTerm p φ) (slab T)
  datum_integrable : ∀ φ, IsSpacetimeTest T φ →
    Integrable (fun x => inner ℝ (u₀ x) (φ (0, x)))
  identity : ∀ φ, IsSpacetimeTest T φ →
    (∫ t in Ioo (0 : ℝ) T, ∫ x : Space, viscosityWeakIntegrand ν u p φ (t, x)) +
      (∫ x : Space, inner ℝ (u₀ x) (φ (0, x))) = 0

@[simp] theorem viscosityWeakIntegrand_one (u : Velocity) (p : Pressure)
    (φ : SpaceTime → Space) : viscosityWeakIntegrand 1 u p φ = weakIntegrand u p φ := by
  funext z
  simp only [viscosityWeakIntegrand, weakIntegrand, one_mul]

/-- At viscosity one this is exactly the equation in the main statement. -/
theorem viscosity_one_iff (T : ℝ) (u₀ : SpatialField) (u : Velocity) (p : Pressure) :
    SolvesNavierStokesViscosity 1 T u₀ u p ↔ SolvesUnforcedNavierStokes T u₀ u p := by
  constructor
  · intro h
    exact ⟨h.temporal_integrable, h.convection_integrable, h.diffusion_integrable,
      h.pressure_integrable, h.datum_integrable, by simpa only [viscosityWeakIntegrand_one] using h.identity⟩
  · intro h
    exact ⟨h.temporal_integrable, h.convection_integrable, h.diffusion_integrable,
      h.pressure_integrable, h.datum_integrable, by simpa only [viscosityWeakIntegrand_one] using h.identity⟩

end UnforcedLeray.ViscosityTransport
