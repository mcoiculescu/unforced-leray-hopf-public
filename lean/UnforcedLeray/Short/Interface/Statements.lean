import UnforcedLeray.Blueprint.Top
import UnforcedLeray.Blueprint.Construction.Cylinder
import UnforcedLeray.Cons.C08PhysicalMode
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# Interface: the energy-class form of `prop:unstable-background` and its bridge to the library

Source of record: `the November 2 reference manuscript` (the 73-page proof).

* `prop:unstable-background`, lines 143-187: `h, 𝒯 > 0`, the DSS field `u_dss` (lines 148-154),
  the background `U_* = H_h[u_dss] + r_heat` (lines 156-165), `0 < σ < 1/4` and a nonzero real
  `𝒯`-periodic solenoidal `b_*` with `b_* ∈ 𝒴_{2,div}`, `∇b_* ∈ 𝒴₂` (lines 167-171), solving
  `σb_* + 𝒯₀b_* - hΔb_* - ½b_* + 𝔓 div(U_*⊗b_* + b_*⊗U_*) = 0` in `𝒟'(ℝ³ × ℝ/𝒯ℤ)` (lines
  173-180), all fields axisymmetric without swirl (lines 181-182).
* The localization module, lines 6001-6340. It starts from the same energy-class mode (the
  proposition `short-loc:reduction`, lines 6008-6070, hypothesis `b, ∇b ∈ L²([0,P]×ℝ³)`), and
  the paragraph "Periodic evolution and regularity of the mode" (lines 6086-6150) is what
  upgrades it. The library's localization half (`Loc/AssemblyB.lean`) takes the graph mode
  `b, hΔb, 𝒯₀b ∈ 𝒴₂`; the bridge below supplies that upgrade by `L²` maximal regularity.

## Contents

1. The source objects of the energy-class proposition (`EnergyData`, `IsPeriodicTest`,
   `SolvesPeriodicModeEquation`, `IsEnergyMode`, `IsUnstableBackgroundEnergy`,
   `ConstructionClaimShort`). Everything not defined here is reused from the library
   (`Blueprint/Package.lean`: `BackgroundCore`, `IsExactBackground`, `IsAxisymmetricNoSwirl`,
   `projectedCoupling`, `periodSlab`) or from the drafts (`Blueprint/Construction/Cylinder.lean`:
   `IsH1Periodic`, `IsWeakModeSolution`, `weakModeIntegrand`, `weakCoupling`).
2. The regular-background class `IsL3Background` (`U ∈ C_per C₀`, `∇U ∈ C_per L³`; lines
   6064-6070) and the leaf Props of the bridge `ConstructionClaimShort → ConstructionClaim`.
3. The leaf Props of the `L²` maximal regularity of the free equation (the window estimate of
   the old manuscript, `paper/main.tex` lines 7479-7517, here for `q = 2`).

No Prop here is proved in this file. The compiled combination is `Compose.lean`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Short.Interface

open UnforcedLeray UnforcedLeray.Blueprint UnforcedLeray.Cons.C08

/-! ## 1. The source objects (lines 143-187) -/

/-- A test field on `ℝ³ × ℝ/𝒯ℤ` (line 180: `𝒟'(ℝ³ × ℝ/𝒯ℤ)`), as a function on `ℝ × ℝ³`
(first coordinate the phase `τ`): smooth, `𝒯`-periodic in `τ`, and supported in a compact set of
space, uniformly in the phase. -/
structure IsPeriodicTest (period : ℝ) (φ : SpaceTime → Space) : Prop where
  smooth : ContDiff ℝ ∞ φ
  periodic : ∀ z : SpaceTime, φ (z.1 + period, z.2) = φ z
  space_compact : ∃ K : Set Space, IsCompact K ∧ ∀ z : SpaceTime, z.2 ∉ K → φ z = 0

/-- The mode equation `loc:eq:mode` (lines 173-180) in `𝒟'(ℝ³ × ℝ/𝒯ℤ)` with the literal Leray
projection: for every periodic test `φ`,
`∫_{(0,𝒯]×ℝ³} [(σ - ½)⟨b,φ⟩ + ⟨b, 𝒯₀ᵗφ⟩ - h⟨b,Δφ⟩] + ∫_0^𝒯 ⟨𝔓 div(U⊗b + b⊗U), φ⟩ dτ = 0`,
where `⟨𝒯₀b, φ⟩ = ⟨b, -∂_τφ + (3/2)φ + ½ y·∇φ⟩` (`driftAdjointTerm`) and
`⟨𝔓 div 𝕋, φ⟩ = -∑_j ⟨𝕋_{·j}, 𝔓∂_jφ⟩` (`projectedCoupling`, `lerayDivPairing`).
Every integrand is integrable for `b ∈ 𝒴₂` and bounded `U` (so no Bochner junk value occurs);
that is proved in the bridge, not assumed here. -/
def SolvesPeriodicModeEquation (h σ period : ℝ) (U b : ℝ → SpatialField) : Prop :=
  ∀ φ : SpaceTime → Space, IsPeriodicTest period φ →
    (∫ z in periodSlab period, weakModeIntegrand h σ b φ z) +
      (∫ τ in Ioc (0 : ℝ) period, projectedCoupling U b φ τ) = 0

/-- The mode half of the data of `prop:unstable-background` in the shorter proof: the exponent
`σ` and the profile `b_*` (lines 167-171). There are no witnesses for `Δb_*` or `𝒯₀b_*`. -/
structure EnergyModeCore where
  /-- The growth exponent `σ` (line 167). -/
  σ : ℝ
  /-- The Floquet profile `b_*(y,τ) = bstar τ y` (line 167). -/
  bstar : ℝ → SpatialField

/-- All objects named by `prop:unstable-background` of the shorter proof. -/
structure EnergyData extends BackgroundCore, EnergyModeCore

/-- The mode clauses of `prop:unstable-background` (lines 167-182), on the background `B`:
`0 < σ < 1/4`; `b_*` is a nonzero real `𝒯`-periodic solenoidal field with `b_* ∈ 𝒴_{2,div}`,
`∇b_* ∈ 𝒴₂` (`IsH1Periodic`); the mode equation holds in `𝒟'(ℝ³ × ℝ/𝒯ℤ)`; and `b_*` is
axisymmetric without swirl at almost every phase. -/
structure IsEnergyMode (B : BackgroundCore) (M : EnergyModeCore) : Prop where
  /-- `0 < σ` (line 167). -/
  σ_pos : 0 < M.σ
  /-- `σ < 1/4` (line 167). -/
  σ_lt : M.σ < 1 / 4
  /-- `b_* ∈ 𝒴_{2,div}` and `∇b_* ∈ 𝒴₂` (lines 169-171). -/
  energy : IsH1Periodic B.period M.bstar
  /-- `b_*` is nonzero (line 167), as an element of `𝒴₂`. -/
  nonzero : ¬ ((fun z : SpaceTime => M.bstar z.1 z.2) =ᵐ[volume.restrict (periodSlab B.period)] 0)
  /-- The mode equation (lines 173-180). -/
  mode_equation : SolvesPeriodicModeEquation B.h M.σ B.period B.Ustar M.bstar
  /-- `b_*` is axisymmetric without swirl (lines 181-182). -/
  symmetric : ∀ᵐ τ, IsAxisymmetricNoSwirl (M.bstar τ)

/-- `prop:unstable-background` of the shorter proof (lines 143-187): the background clauses are
those of the library (`IsExactBackground`: `h, 𝒯 > 0`, `u_dss`, `U_* = H_h[u_dss] + r_heat`,
the background equation, the symmetries), the mode clauses are the energy-class ones. -/
def IsUnstableBackgroundEnergy (D : EnergyData) : Prop :=
  IsExactBackground D.toBackgroundCore ∧ IsEnergyMode D.toBackgroundCore D.toEnergyModeCore

/-- The analytic construction needed for localization (lines 143-187). -/
def ConstructionClaimShort : Prop :=
  ∃ D : EnergyData, IsUnstableBackgroundEnergy D

/-! ## 2. The bridge to the graph-mode package -/

/-- A regular periodic background, the class used in the localization module (lines 6064-6070):
`U ∈ C_per C₀` (continuous in space, bounded, jointly measurable, `𝒯`-periodic) and
`∇U ∈ C_per L³`, with `dU j` the weak derivative `∂_jU` at every phase. -/
structure IsL3Background (period : ℝ) (U : ℝ → SpatialField)
    (dU : Fin 3 → ℝ → SpatialField) : Prop where
  periodic : Function.Periodic U period
  continuous : ∀ τ, Continuous (U τ)
  bounded : ∃ C : ℝ, ∀ τ y, ‖U τ y‖ ≤ C
  measurable : AEStronglyMeasurable (fun z : SpaceTime => U z.1 z.2) volume
  derivative_periodic : ∀ j, Function.Periodic (dU j) period
  derivative_measurable :
    ∀ j, AEStronglyMeasurable (fun z : SpaceTime => dU j z.1 z.2) volume
  weak_derivative : ∀ τ j, HasWeakSpatialDerivative j (U τ) (dU j τ)
  derivative_L3 : ∃ C : ℝ, ∀ τ j, MemLp (dU j τ) 3 volume ∧
    eLpNorm (dU j τ) 3 volume ≤ ENNReal.ofReal C

/-- **Leaf 1** (lines 6064-6070: "Gaussian convolution and the bounds on `a` give ... Hence
`U ∈ C_per C₀`, `∇U ∈ C_per L³`"). A continuous periodic `C₀`-valued path `V` representing the
fields `U τ`, with a continuous periodic `L³`-valued path `W` of their weak first derivatives,
gives the regular background `V` with jointly measurable periodic weak derivatives. -/
def L3BackgroundOfPath : Prop :=
  ∀ (P : ℝ) (U : ℝ → SpatialField) (V : ℝ → ZeroAtInftyContinuousMap Space Space)
    (W : ℝ → Fin 3 → Lp Space 3 (volume : Measure Space)),
    0 < P → Continuous V → Function.Periodic V P →
    (∀ τ, (V τ : SpatialField) =ᵐ[volume] U τ) →
    Continuous W → Function.Periodic W P →
    (∀ τ i, HasWeakSpatialDerivative i (U τ) (W τ i : SpatialField)) →
    ∃ dV : Fin 3 → ℝ → SpatialField, IsL3Background P (fun τ => (V τ : SpatialField)) dV

/-- **Leaf 2** (the mode-equation formulation, line 180): for a regular background and an
energy-class periodic `b`, the equation in `𝒟'(ℝ³ × ℝ/𝒯ℤ)` gives the equation in distributions
on `ℝ × ℝ³` (the library's `IsWeakModeSolution`, compactly supported tests). Proof by
periodization of the test (`periodizeTest`); the helper Props of Section 2b isolate its steps. -/
def PeriodicModeEquationToLine : Prop :=
  ∀ (h σ P : ℝ) (U : ℝ → SpatialField) (dU : Fin 3 → ℝ → SpatialField) (b : ℝ → SpatialField),
    0 < P → IsL3Background P U dU → IsH1Periodic P b →
    SolvesPeriodicModeEquation h σ P U b → IsWeakModeSolution h σ U b

/-- **Leaf 3** (lines 6071-6075: "For the first bound use `‖U‖_∞‖∇f‖₂ + ‖∇U‖₃‖f‖₆`"). On a regular
background and for `w` in the periodic `H¹` class, the body force
`g = Σ_j ∂_j(w_jU + U_jw) = U·∇w + w·∇U` is in `𝒴₂` and `⟨𝔓 div(U⊗w + w⊗U), ψ⟩ = ⟨𝔓 g, ψ⟩` at
almost every phase for every similarity test `ψ` (generalizes the draft `exists_bodyForce`,
which assumed `∇U` bounded, to `∇U ∈ L³` via `H¹ ⊂ L⁶`). -/
def BodyForceL3 : Prop :=
  ∀ (P : ℝ) (U : ℝ → SpatialField) (dU : Fin 3 → ℝ → SpatialField) (w : ℝ → SpatialField),
    0 < P → IsL3Background P U dU → IsH1Periodic P w →
    ∃ g : ℝ → SpatialField, B0005.IsY2 P g ∧
      ∀ᵐ τ, MemLp (w τ) 2 volume ∧ ∀ ψ, IsSimilarityTest ψ →
        weakCoupling U w ψ τ =
          inner ℝ (Leray.projection (toL2 (g τ))) (toL2 (slice ψ τ))

/-! ### 2b. Helper Props for Leaf 2 (periodization of a compactly supported test) -/

/-- The periodization `Σ_{k∈ℤ} ψ(τ + k𝒯, y)` of a function on `ℝ × ℝ³` (a finite sum at each
point when `ψ` has compact support). -/
def periodizeTest (P : ℝ) (ψ : SpaceTime → Space) (z : SpaceTime) : Space :=
  ∑ᶠ k : ℤ, ψ (z.1 + (k : ℝ) * P, z.2)

/-- Helper 2b-1: the periodization of a similarity test is a periodic test. -/
def PeriodizeIsPeriodicTest : Prop :=
  ∀ (P : ℝ) (ψ : SpaceTime → Space), 0 < P → IsSimilarityTest ψ →
    IsPeriodicTest P (periodizeTest P ψ)

/-- Helper 2b-2: the differential expressions of the mode equation commute with
periodization. -/
def PeriodizeCommutes : Prop :=
  ∀ (P : ℝ) (ψ : SpaceTime → Space), 0 < P → IsSimilarityTest ψ → ∀ z : SpaceTime,
    timeDerivative (periodizeTest P ψ) z.1 z.2 =
        ∑ᶠ k : ℤ, timeDerivative ψ (z.1 + (k : ℝ) * P) z.2 ∧
    spatialLaplacian (periodizeTest P ψ) z.1 z.2 =
        ∑ᶠ k : ℤ, spatialLaplacian ψ (z.1 + (k : ℝ) * P) z.2 ∧
    spatialDerivative (periodizeTest P ψ) z.1 z.2 z.2 =
        ∑ᶠ k : ℤ, spatialDerivative ψ (z.1 + (k : ℝ) * P) z.2 z.2

/-- Helper 2b-3: for a periodic `𝒴₂` field `f` and a continuous compactly supported `g`, the
line integral of `⟨f, g⟩` over `ℝ × ℝ³` is the slab integral of `⟨f, periodizeTest P g⟩`, and the
latter integrand is integrable on the slab. -/
def PeriodicLineToSlab : Prop :=
  ∀ (P : ℝ) (f : ℝ → SpatialField) (g : SpaceTime → Space), 0 < P → B0005.IsY2 P f →
    Continuous g → HasCompactSupport g →
    IntegrableOn (fun z : SpaceTime => inner ℝ (f z.1 z.2) (periodizeTest P g z))
        (periodSlab P) volume ∧
      (∫ z : SpaceTime, inner ℝ (f z.1 z.2) (g z)) =
        ∫ z in periodSlab P, inner ℝ (f z.1 z.2) (periodizeTest P g z)

/-- Helper 2b-4: the Leray coupling pairing, in its Lebesgue form on the line, equals the
literal pairing of the periodized test over one period (the columns of `U⊗b + b⊗U` are in `L²`
at almost every phase because `U` is bounded and `b(τ) ∈ L²`). -/
def PeriodicCouplingTransfer : Prop :=
  ∀ (P : ℝ) (V : ℝ → SpatialField) (dV : Fin 3 → ℝ → SpatialField) (b : ℝ → SpatialField),
    0 < P → IsL3Background P V dV → B0005.IsY2 P b → ∀ ψ, IsSimilarityTest ψ →
      (∫ τ, weakCoupling V b ψ τ) =
        ∫ τ in Ioc (0 : ℝ) P, projectedCoupling V b (periodizeTest P ψ) τ

/-- Helper 2b-5: the integrability clauses of `IsWeakModeSolution` for a periodic `H¹` field on a
regular background. -/
def ModeSolutionIntegrability : Prop :=
  ∀ (P : ℝ) (V : ℝ → SpatialField) (dV : Fin 3 → ℝ → SpatialField) (b : ℝ → SpatialField),
    0 < P → IsL3Background P V dV → IsH1Periodic P b → ∀ ψ, IsSimilarityTest ψ →
      Integrable (pairTerm b ψ) ∧ Integrable (temporalTerm b ψ) ∧
      Integrable (dilationTerm b ψ) ∧ Integrable (diffusionTerm b ψ) ∧
      (∀ᵐ τ, ∀ j : Fin 3,
        Integrable (lerayDivIntegrand (symTensorColumns (V τ) (b τ)) (slice ψ τ) j)) ∧
      Integrable (weakCoupling V b ψ)

/-! ## 3. `L²` maximal regularity of the free equation (replaces `FreeLaplacianRegularity`) -/

/-- The open space-time window `(τ₀ - r, τ₀ + r) × ℝ³`. -/
def windowSlab (τ₀ r : ℝ) : Set SpaceTime := Ioo (τ₀ - r) (τ₀ + r) ×ˢ univ

/-- **Leaf 4a, the fixed-window Laplacian estimate** (old manuscript `paper/main.tex` lines
7479-7517, `eq:free-stress-13`, `-14`, `-15`, blueprint B0424, for `q = 2`; the existence half).
A `𝒯`-periodic `𝒴₂` solution `w` of the free equation `(μ + 𝒯₀ - hΔ - ½)w + 𝔓g = 0` in
distributions on `ℝ × ℝ³`, with `g ∈ 𝒴₂`, has on every window `|τ - τ₀| < 1` a Laplacian in
`L²`: `Λ` with `∫∫⟨w, Δψ⟩ = ∫∫⟨Λ, ψ⟩` for tests supported in the window. Proof: the chart
`v(t,x) = e^{-t/2}w(τ₀ + t, e^{-t/2}x)`, the time change `θ = e^t` and a time cutoff turn the
equation into `(∂_θ - hΔ_x)u = F` with `u, F ∈ L²(ℝ × ℝ³)`; then the compiled heat maximal
regularity (`Units/B0423.lean`, `heat_estimate_laplacian`) gives `Δ_xu ∈ L²`. -/
def FreeWindowRegularity : Prop :=
  ∀ (h μ P : ℝ) (w g : ℝ → SpatialField), 0 < h → 0 < P →
    B0005.IsY2 P w → B0005.IsY2 P g → IsWeakFreeSolution h μ w g →
    ∀ τ₀ : ℝ, ∃ Λ : ℝ → SpatialField,
      MemLp (fun z : SpaceTime => Λ z.1 z.2) 2 (volume.restrict (windowSlab τ₀ 1)) ∧
      ∀ ψ, IsSimilarityTest ψ → tsupport ψ ⊆ windowSlab τ₀ 1 → laplacianPairing w Λ ψ

/-- **Leaf 4b, patching the windows** (the passage from `eq:free-stress-15` to the global
statement, old manuscript lines 7519-7536, blueprint B0425-B0426, B0438, where the periodic
center-averaging identity is used only to bound the norm; for membership in `𝒴₂` it is enough
that `w, g` are in `L²` on every bounded window): the window Laplacians agree almost everywhere on
overlaps (fundamental lemma on the open overlap), glue to a locally square integrable field,
which is `𝒯`-periodic almost everywhere and is re-chosen periodic by `periodize`
(`Cons/C08PhysicalMode/Slices.lean`). Gives the draft hypothesis `FreeLaplacianRegularity`. -/
def WindowsToGlobalLaplacian : Prop :=
  FreeWindowRegularity → FreeLaplacianRegularity

end UnforcedLeray.Short.Interface
