import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# The statement of manuscript Theorem A

This module defines the requested assertion. It does not prove existence of its
witnesses. Every analytic predicate below uses ordinary Lebesgue integrals,
Fréchet derivatives of test functions, and Mathlib's `Lp` spaces on Euclidean R³.
There is no construction axiom or abstract solution predicate.

A first derivative is a vector field for each coordinate direction. A second
derivative is a vector field for each ordered pair of coordinate directions.
Continuity of all these finitely many L² components on a positive closed time
interval expresses continuity in the H² graph norm. Using ordered second
partials duplicates the mixed partials in the usual multi-index norm, giving
an equivalent finite-dimensional sum norm and exactly the same topology.

Spacetime test functions are globally smooth compactly supported extensions,
vanishing at times at or after T. Their restrictions to [0,T) are the usual
test functions allowing a nonzero trace at the initial time.

The datum and both solutions are axisymmetric without swirl: invariant under the
group 𝒪 of linear isometries fixing e₃, acting by (g·f)(x) = g (f (g⁻¹ x)).
Invariance is almost everywhere for each g, since the fields are L² representatives.

The proposition `MainClaim` encodes Theorem A of the November 2, 2026
reference manuscript, including its symmetry clause and initial weak
formulation. The unconditional proof is `UnforcedLeray.main_theorem`
in the root module.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray

abbrev Space := EuclideanSpace ℝ (Fin 3)
abbrev SpaceTime := ℝ × Space
abbrev SpatialField := Space → Space
abbrev Velocity := ℝ → SpatialField
abbrev Pressure := ℝ → Space → ℝ
abbrev FirstDerivatives := ℝ → Fin 3 → SpatialField
abbrev SecondDerivatives := ℝ → Fin 3 → Fin 3 → SpatialField
abbrev L2Space := Lp Space 2 (volume : Measure Space)

def coordinateVector (i : Fin 3) : Space := EuclideanSpace.single i 1

def spatialTestDerivative (i : Fin 3) (φ : Space → ℝ) (x : Space) : ℝ :=
  fderiv ℝ φ x (coordinateVector i)

structure IsSpatialTest (φ : Space → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ φ
  compact : HasCompactSupport φ

/-- A genuine distributional coordinate derivative, with convergent pairings. -/
structure HasWeakSpatialDerivative (i : Fin 3) (f g : SpatialField) : Prop where
  left_integrable : ∀ φ, IsSpatialTest φ →
    Integrable (fun x => spatialTestDerivative i φ x • f x)
  right_integrable : ∀ φ, IsSpatialTest φ → Integrable (fun x => φ x • g x)
  identity : ∀ φ, IsSpatialTest φ →
    (∫ x, spatialTestDerivative i φ x • f x) = -(∫ x, φ x • g x)

/-- Distributional divergence zero, including convergence of the pairing. -/
structure IsSolenoidal (f : SpatialField) : Prop where
  integrable : ∀ φ, IsSpatialTest φ →
    Integrable (fun x => ∑ i : Fin 3, (f x) i * spatialTestDerivative i φ x)
  identity : ∀ φ, IsSpatialTest φ →
    (∫ x, ∑ i : Fin 3, (f x) i * spatialTestDerivative i φ x) = 0

def l2Norm (f : SpatialField) : ℝ := (eLpNorm f 2 volume).toReal

open Classical in
/-- Conversion to the L² quotient; consumers require `MemLp` on their domain. -/
def toL2 (f : SpatialField) : L2Space :=
  if h : MemLp f 2 volume then h.toLp f else 0

/-- The squared Frobenius L² norm of the spatial gradient. -/
def dissipation (G : FirstDerivatives) (t : ℝ) : ℝ :=
  ∑ i : Fin 3, l2Norm (G t i) ^ 2

structure IsInitialDatum (u₀ : SpatialField) : Prop where
  memLp : MemLp u₀ 2 volume
  compact : HasCompactSupport u₀
  solenoidal : IsSolenoidal u₀
  nonzero : 0 < l2Norm u₀

def slab (T : ℝ) : Set SpaceTime := Ioo (0 : ℝ) T ×ˢ univ

structure IsSpacetimeTest (T : ℝ) (φ : SpaceTime → Space) : Prop where
  smooth : ContDiff ℝ ∞ φ
  compact : HasCompactSupport φ
  timeSupport : tsupport φ ⊆ Iio T ×ˢ univ

def timeDerivative (φ : SpaceTime → Space) (t : ℝ) (x : Space) : Space :=
  fderiv ℝ (fun s => φ (s, x)) t 1

def spatialDerivative (φ : SpaceTime → Space) (t : ℝ) (x : Space) : Space →L[ℝ] Space :=
  fderiv ℝ (fun y => φ (t, y)) x

def spatialLaplacian (φ : SpaceTime → Space) (t : ℝ) (x : Space) : Space :=
  ∑ i : Fin 3, fderiv ℝ (fun y => spatialDerivative φ t y (coordinateVector i))
    x (coordinateVector i)

def spatialDivergence (φ : SpaceTime → Space) (t : ℝ) (x : Space) : ℝ :=
  ∑ i : Fin 3, (spatialDerivative φ t x (coordinateVector i)) i

def temporalTerm (u : Velocity) (φ : SpaceTime → Space) (z : SpaceTime) : ℝ :=
  inner ℝ (u z.1 z.2) (timeDerivative φ z.1 z.2)

/-- `u · (Dφ u) = ∑ᵢⱼ uᵢ uⱼ ∂ⱼφᵢ`, with the manuscript's tensor convention. -/
def convectionTerm (u : Velocity) (φ : SpaceTime → Space) (z : SpaceTime) : ℝ :=
  inner ℝ (u z.1 z.2) (spatialDerivative φ z.1 z.2 (u z.1 z.2))

def diffusionTerm (u : Velocity) (φ : SpaceTime → Space) (z : SpaceTime) : ℝ :=
  inner ℝ (u z.1 z.2) (spatialLaplacian φ z.1 z.2)

def pressureTerm (p : Pressure) (φ : SpaceTime → Space) (z : SpaceTime) : ℝ :=
  p z.1 z.2 * spatialDivergence φ z.1 z.2

def weakIntegrand (u : Velocity) (p : Pressure) (φ : SpaceTime → Space)
    (z : SpaceTime) : ℝ :=
  temporalTerm u φ z + convectionTerm u φ z + diffusionTerm u φ z + pressureTerm p φ z

/-- The full, zero-force, viscosity-one momentum equation including the initial datum. -/
structure SolvesUnforcedNavierStokes (T : ℝ) (u₀ : SpatialField)
    (u : Velocity) (p : Pressure) : Prop where
  temporal_integrable : ∀ φ, IsSpacetimeTest T φ → IntegrableOn (temporalTerm u φ) (slab T)
  convection_integrable : ∀ φ, IsSpacetimeTest T φ → IntegrableOn (convectionTerm u φ) (slab T)
  diffusion_integrable : ∀ φ, IsSpacetimeTest T φ → IntegrableOn (diffusionTerm u φ) (slab T)
  pressure_integrable : ∀ φ, IsSpacetimeTest T φ → IntegrableOn (pressureTerm p φ) (slab T)
  datum_integrable : ∀ φ, IsSpacetimeTest T φ →
    Integrable (fun x => inner ℝ (u₀ x) (φ (0, x)))
  identity : ∀ φ, IsSpacetimeTest T φ →
    (∫ t in Ioo (0 : ℝ) T, ∫ x : Space, weakIntegrand u p φ (t, x)) +
      (∫ x : Space, inner ℝ (u₀ x) (φ (0, x))) = 0

/-- The exact regularity, equation, trace and energy conclusions for one solution.
The witnesses G and H are actual weak derivatives, not unspecified operators. -/
structure IsTheoremASolution (T : ℝ) (u₀ : SpatialField) (u : Velocity)
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
  equation : SolvesUnforcedNavierStokes T u₀ u p
  energy_equality : ∀ t₀ t₁, 0 ≤ t₀ → t₀ ≤ t₁ → t₁ ≤ T →
    (1 / 2 : ℝ) * l2Norm (u t₁) ^ 2 + (∫ t in Ioo t₀ t₁, dissipation G t) =
      (1 / 2 : ℝ) * l2Norm (u t₀) ^ 2

/-- A member of the manuscript's group 𝒪: a linear isometry of R³ fixing e₃.
The reflections in planes containing the axis are included. -/
def FixesAxis (g : Space ≃ₗᵢ[ℝ] Space) : Prop :=
  g (coordinateVector 2) = coordinateVector 2

/-- Axisymmetric without swirl: 𝒪-invariant under (g·f)(x) = g (f (g⁻¹ x)). -/
def IsAxisymmetricNoSwirl (f : SpatialField) : Prop :=
  ∀ g : Space ≃ₗᵢ[ℝ] Space, FixesAxis g →
    (fun x => g (f (g.symm x))) =ᵐ[volume] f

/-- The manuscript's full existential Theorem A, with no construction hypothesis. -/
def MainClaim : Prop :=
  ∃ (T : ℝ) (u₀ : SpatialField) (u₁ u₂ : Velocity) (p₁ p₂ : Pressure)
      (G₁ G₂ : FirstDerivatives) (H₁ H₂ : SecondDerivatives) (c σ : ℝ),
    0 < T ∧ IsInitialDatum u₀ ∧
    IsTheoremASolution T u₀ u₁ p₁ G₁ H₁ ∧ IsTheoremASolution T u₀ u₂ p₂ G₂ H₂ ∧
    0 < c ∧ 0 < σ ∧ σ < 1 / 4 ∧
    (∀ t ∈ Ioc (0 : ℝ) T,
      c * Real.rpow t (σ + 1 / 4) ≤ l2Norm (u₂ t - u₁ t)) ∧
    IntegrableOn (fun t => l2Norm (u₂ t - u₁ t) ^ 2) (Ioo (0 : ℝ) T) ∧
    c ^ 2 * Real.rpow T (2 * σ + 3 / 2) / (2 * σ + 3 / 2) ≤
      (∫ t in Ioo (0 : ℝ) T, l2Norm (u₂ t - u₁ t) ^ 2) ∧
    0 < c ^ 2 * Real.rpow T (2 * σ + 3 / 2) / (2 * σ + 3 / 2) ∧
    IsAxisymmetricNoSwirl u₀ ∧
    (∀ t ∈ Icc (0 : ℝ) T, IsAxisymmetricNoSwirl (u₁ t)) ∧
    (∀ t ∈ Icc (0 : ℝ) T, IsAxisymmetricNoSwirl (u₂ t))

/-- Zero norm cannot satisfy the nonzero initial-data condition. -/
theorem IsInitialDatum.norm_ne_zero {u₀ : SpatialField} (h : IsInitialDatum u₀) :
    l2Norm u₀ ≠ 0 := ne_of_gt h.nonzero

/-- The specified dissipation is nonnegative, independently of regularity. -/
theorem dissipation_nonneg (G : FirstDerivatives) (t : ℝ) : 0 ≤ dissipation G t := by
  exact Finset.sum_nonneg (fun i _ => sq_nonneg (l2Norm (G t i)))

/-- The quotient conversion retains the actual field wherever the L² guard holds. -/
theorem toL2_of_memLp {f : SpatialField} (hf : MemLp f 2 volume) :
    toL2 f = hf.toLp f := by
  unfold toL2
  rw [dite_eq_left hf]

theorem coeFn_toL2 {f : SpatialField} (hf : MemLp f 2 volume) :
    (toL2 f : SpatialField) =ᵐ[volume] f := by
  rw [toL2_of_memLp hf]
  exact hf.coeFn_toLp

theorem norm_toL2 {f : SpatialField} (hf : MemLp f 2 volume) :
    ‖toL2 f‖ = l2Norm f := by
  rw [toL2_of_memLp hf]
  exact Lp.norm_toLp f hf

@[simp] theorem l2Norm_zero : l2Norm (0 : SpatialField) = 0 := by
  simp [l2Norm]

/-- Nonzero means nonzero as an L² equivalence class, not at an isolated point. -/
theorem IsInitialDatum.not_ae_zero {u₀ : SpatialField} (h : IsInitialDatum u₀) :
    ¬ u₀ =ᵐ[volume] (0 : SpatialField) := by
  intro hz
  have he : l2Norm u₀ = 0 := by
    unfold l2Norm
    rw [eLpNorm_congr_ae hz]
    simp
  exact h.norm_ne_zero he

end UnforcedLeray
