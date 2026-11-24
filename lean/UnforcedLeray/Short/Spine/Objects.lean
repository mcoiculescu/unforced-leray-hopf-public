import UnforcedLeray.Blueprint.Package
import UnforcedLeray.Blueprint.Construction.Planar
import UnforcedLeray.Blueprint.Construction.Cylinder
import UnforcedLeray.Blueprint.Construction.Steps
import UnforcedLeray.Units.B0140
import UnforcedLeray.Cons.C03Background.RawLift

/-!
# Shared objects of the four-part construction (shorter proof)

Source of record: `the November 2 reference manuscript` (73 pages).

* `prop:unstable-background`, lines 145-188: the exact background `(h, 𝒯, u_dss, U_*, r_heat)`
  (the library's `Blueprint.IsExactBackground`, reused unchanged) and the **energy-class**
  Floquet mode `b_*` with `b_* ∈ 𝒴_{2,div}`, `∇b_* ∈ 𝒴₂`, `0 < σ < 1/4` (lines 167-184).
  The library's `Blueprint.IsGrowingMode` requires the graph class `hΔb_*, 𝒯₀b_* ∈ 𝒴₂`
  (old manuscript); the shorter proof only has the energy class, so this file defines
  `IsEnergyMode`, `IsUnstableBackgroundEnergy` and `ConstructionClaimShort` (existence of data).
* The train (`B0140.TrainSol`), the planar reference (`Planar.PlanarData`), the ring lift
  (`Axi.Nv`, `Cons.C03.rawProfile`) are the library/draft objects; nothing is redefined.
* The parameters of a level: the period `P = 2εc` (`shortPeriod`), the loss
  `ρ = P_νε^{3/11}e^{m/ν}` (`lossRadius`) and the entrance bound `P_νe^{m/ν}ε` (`entranceRadius`).
* The exact background of one level, as Part II constructs it around one fixed inlet
  (lines 2316-2318, 2505-2524, 2664-2713, 5951-5954), and the predicate `IsShortBackground` of
  everything Part II delivers to Part III, are in `Short/Spine/Background.lean`, in the Part II-b
  encoding (`Short/PartII-b/StatementsNonlinear.lean`); they are kept out of this file so that the
  Part I files, which import it, do not import Part II-b.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Short.Spine

open UnforcedLeray UnforcedLeray.Blueprint UnforcedLeray.Blueprint.Planar

/-! ## The energy-class Floquet mode (lines 167-188) -/

/-- Membership of a `𝒯`-periodic field in `𝒴₂ = L²([0,𝒯], dτ/𝒯; L²(ℝ³))` (lines 136-141): the
tensor-valued space of `∇b_*` is handled by applying this to each partial derivative. -/
structure IsY2 (period : ℝ) (f : ℝ → SpatialField) : Prop where
  periodic : Function.Periodic f period
  measurable : AEStronglyMeasurable (fun z : SpaceTime => f z.1 z.2) volume
  memL2 : MemLp (fun z : SpaceTime => f z.1 z.2) 2 (volume.restrict (periodSlab period))

/-- The linear part of `σb + 𝒯₀b - hΔb - ½b + 𝔓div(U⊗b + b⊗U) = 0` (`loc:eq:mode`, lines
177-184) tested against `ψ`, with `𝒯₀ = ∂_τ - ½y·∇` and `Δ` moved onto `ψ` (no graph witnesses:
`b_*` is only in the energy class). -/
def energyModeIntegrand (h σ : ℝ) (b : ℝ → SpatialField) (ψ : SpaceTime → Space)
    (z : SpaceTime) : ℝ :=
  σ * pairTerm b ψ z + driftAdjointTerm b ψ z - h * diffusionTerm b ψ z -
    (1 / 2 : ℝ) * pairTerm b ψ z

/-- `loc:eq:mode` in `𝒟'(ℝ³ × ℝ/𝒯ℤ)` with the literal Leray projection `lerayDivPairing`,
every pairing convergent. -/
structure SolvesEnergyModeEquation (h σ : ℝ) (U b : ℝ → SpatialField) : Prop where
  tensor_memL2 : ∀ᵐ τ, ColumnsL2 (symTensorColumns (U τ) (b τ))
  value_integrable : ∀ ψ, IsSimilarityTest ψ → Integrable (pairTerm b ψ)
  temporal_integrable : ∀ ψ, IsSimilarityTest ψ → Integrable (temporalTerm b ψ)
  diffusion_integrable : ∀ ψ, IsSimilarityTest ψ → Integrable (diffusionTerm b ψ)
  dilation_integrable : ∀ ψ, IsSimilarityTest ψ → Integrable (dilationTerm b ψ)
  coupling_integrable : ∀ ψ, IsSimilarityTest ψ → Integrable (projectedCoupling U b ψ)
  identity : ∀ ψ, IsSimilarityTest ψ →
    (∫ z, energyModeIntegrand h σ b ψ z) + (∫ τ, projectedCoupling U b ψ τ) = 0

/-- `loc:eq:energy-mode` and `loc:eq:mode` for `b` on the background `U`, lines 167-189:
`b ∈ 𝒴_{2,div}` nonzero, `∇b ∈ 𝒴₂` (`G τ i = ∂_i b(τ)` weakly), the equation, and the
symmetry of `b_*`. -/
structure IsEnergyMode (h period σ : ℝ) (U b : ℝ → SpatialField)
    (G : ℝ → Fin 3 → SpatialField) : Prop where
  value : IsY2Div period b
  gradient : ∀ i : Fin 3, IsY2 period (fun τ => G τ i)
  gradient_weak : ∀ᵐ τ, ∀ i : Fin 3, HasWeakSpatialDerivative i (b τ) (G τ i)
  nonzero : ¬ ((fun z : SpaceTime => b z.1 z.2) =ᵐ[volume.restrict (periodSlab period)] 0)
  equation : SolvesEnergyModeEquation h σ U b
  symmetric : ∀ᵐ τ, IsAxisymmetricNoSwirl (b τ)

/-- The mode half of the data of `prop:unstable-background` in the energy class. -/
structure EnergyModeCore where
  /-- The growth exponent `σ` (line 167). -/
  σ : ℝ
  /-- The Floquet profile `b_*` (line 167). -/
  bstar : ℝ → SpatialField
  /-- The weak gradient `∇b_*`, `grad τ i = ∂_i b_*(τ)`. -/
  grad : ℝ → Fin 3 → SpatialField

/-- The mode clauses of `prop:unstable-background` (lines 167-189) on the background `B`. -/
structure IsEnergyGrowingMode (B : BackgroundCore) (M : EnergyModeCore) : Prop where
  σ_pos : 0 < M.σ
  σ_lt : M.σ < 1 / 4
  mode : IsEnergyMode B.h B.period M.σ B.Ustar M.bstar M.grad

/-- `prop:unstable-background` of the shorter proof, lines 145-188, for one data record. -/
def IsUnstableBackgroundEnergy (B : BackgroundCore) (M : EnergyModeCore) : Prop :=
  IsExactBackground B ∧ IsEnergyGrowingMode B M

/-- Existence of data for `prop:unstable-background` of the shorter proof (lines 145-188):
the output of the construction (Parts I-III), the input of the localization (Part IV). -/
def ConstructionClaimShort : Prop :=
  ∃ (B : BackgroundCore) (M : EnergyModeCore), IsUnstableBackgroundEnergy B M

/-! ## The parameters of a level (lines 2028-2040, 5835-5985) -/

/-- The background period `P = 2εc` with `c = ν^{-2}` (line 2033 and line 2079 of the old
numbering: the ring-lift period is `2c/R = 2εc`). -/
def shortPeriod (ν ε : ℝ) : ℝ := 2 * ε * Train.per ν

/-- The loss `ρ = P_ν ε^{3/11} e^{m/ν}` with the fixed polynomial `P_ν = C ν^{-N}` (lines
2490-2495, 2697-2700, 5128-5135). -/
def lossRadius (ν ε m C : ℝ) (N : ℕ) : ℝ := C * (ν ^ N)⁻¹ * Real.exp (m / ν) * ε ^ (3 / 11 : ℝ)

/-- The entrance-coefficient bound `|α| ≤ P_ν e^{m/ν} ε` (`short-bg:result`, line 2523). -/
def entranceRadius (ν ε m C : ℝ) (N : ℕ) : ℝ := C * (ν ^ N)⁻¹ * Real.exp (m / ν) * ε

end UnforcedLeray.Short.Spine
