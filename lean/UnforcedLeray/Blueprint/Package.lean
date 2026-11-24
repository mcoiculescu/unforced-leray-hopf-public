import UnforcedLeray.Statement
import UnforcedLeray.Analysis.Heat.Averaging
import UnforcedLeray.Analysis.LerayProjection.WeakStress.Dual
import UnforcedLeray.Analysis.SobolevGraph.H2
import UnforcedLeray.Analysis.Heat.Kernel
import Mathlib.Analysis.SpecialFunctions.Pow.Integral

/-!
# The hypothesis package of `thm:localization` (final interface)

`paper/main.tex`, Proposition `prop:unstable-background`, lines 150–191, with the
definitions it uses from lines 107–117 (`(u⊗v)_{ij} = u_i v_j`, `(div 𝕋)_i = ∂_j 𝕋_{ij}`, the
Leray projection `𝔓`, the group `𝒪`) and lines 136–147 (`𝒴_q`, `𝒯₀`, the periodic graph).
Blueprint units: B0005 (`unlabeled:136`), B0706 (`loc:eq:dss`), B0707 (`unlabeled:160`,
the heat profile), B0708 (`loc:eq:background`), B1007 (`loc:eq:graph`, `loc:eq:mode`),
B1008 (`unlabeled:188`, symmetry) and B1034 (`prop:unstable-background`). The predicate is
the definition unit asked for in `blueprint/critic.md` §2: it depends only on the group `𝒪`
(B0003) and the graph spaces (B0005).

This module asserts nothing about existence. `IsUnstableBackground` is a definition;
the existence statement is `ConstructionClaim` in `Blueprint/Top.lean`, which is OPEN.



* Profiles are functions `τ ↦ (y ↦ value)`, `ℝ → SpatialField`; spacetime pairings are
  Lebesgue integrals on `SpaceTime = ℝ × Space`.
* `𝔓 div 𝕋` is literal: `⟨𝔓 div 𝕋, φ⟩ = -∑_j ⟨𝕋_{·j}, 𝔓 ∂_j φ⟩` with the compiled `L²`
  Leray projection `Leray.projection` (`lerayDivPairing`). Both profile equations are tested
  against all smooth compactly supported fields, not only divergence-free ones. The pairing
  agrees with the compiled `Leray.WeakStress.projectedDivergence`
  (`lerayDivPairing_eq_projectedDivergence`, proved below).
* Every pairing has its own integrability clause, and every tensor whose columns enter
  `toL2` has an `L²` clause, so neither the Bochner junk value `0` nor the `toL2` junk value
  can make an identity hold.
* The graph `loc:eq:graph` uses two witness fields `lapB = Δb_*` and
  `driftB = 𝒯₀ b_* = (∂_τ - ½ y·∇) b_*`, each fixed by a two-sided distributional identity
  against all spacetime tests.
* `r_heat` is a continuous periodic path in the compiled `SobolevGraph.H2`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Metric
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Blueprint

/-! ## Test fields and the literal `𝔓 div` (lines 107–110) -/

/-- A smooth compactly supported spatial vector test field `φ ∈ C_c^∞(ℝ³;ℝ³)`. -/
structure IsVectorTest (φ : Space → Space) : Prop where
  smooth : ContDiff ℝ ∞ φ
  compact : HasCompactSupport φ

/-- A smooth compactly supported vector test field on `ℝ_τ × ℝ³_y` (first coordinate `τ`).
"In distributions" in lines 164–185 means testing against these. -/
structure IsSimilarityTest (ψ : SpaceTime → Space) : Prop where
  smooth : ContDiff ℝ ∞ ψ
  compact : HasCompactSupport ψ

/-- The phase slice `y ↦ ψ(τ, y)` of a similarity test. -/
def slice (ψ : SpaceTime → Space) (τ : ℝ) : Space → Space := fun y => ψ (τ, y)

/-- The coordinate derivative `∂_j φ` of a spatial vector field. -/
def testPartial (φ : Space → Space) (j : Fin 3) : SpatialField :=
  fun y => fderiv ℝ φ y (coordinateVector j)

/-- Column `j` of `u ⊗ v`, `(u ⊗ v)_{kj} = u_k v_j` (line 107): the field `v_j u`. -/
def tensorColumns (u v : SpatialField) (j : Fin 3) : SpatialField :=
  fun y => (v y) j • u y

/-- Column `j` of `u ⊗ v + v ⊗ u`: the field `v_j u + u_j v`. -/
def symTensorColumns (u v : SpatialField) (j : Fin 3) : SpatialField :=
  fun y => (v y) j • u y + (u y) j • v y

/-- The three columns of a tensor lie in `L²`. -/
def ColumnsL2 (col : Fin 3 → SpatialField) : Prop := ∀ j, MemLp (col j) 2 volume

/-- `⟨𝔓 div 𝕋, φ⟩ = ⟨div 𝕋, 𝔓 φ⟩ = -∑_j ⟨𝕋_{·j}, 𝔓 ∂_j φ⟩` for a tensor with columns `col`
(lines 107–110). Consumers always require `ColumnsL2 col`; `∂_j φ` is in `L²` for a test. -/
def lerayDivPairing (col : Fin 3 → SpatialField) (φ : Space → Space) : ℝ :=
  -∑ j : Fin 3, inner ℝ (toL2 (col j)) (Leray.projection (toL2 (testPartial φ j)))

/-- The literal pairing is the compiled projected weak divergence, evaluated on any weak `H¹`
field whose derivatives are those of `φ`. -/
theorem lerayDivPairing_eq_projectedDivergence (col : Fin 3 → SpatialField)
    (φ : Space → Space) (F : SobolevGraph.H1)
    (hF : ∀ j, F.derivative j = toL2 (testPartial φ j)) :
    lerayDivPairing col φ =
      Leray.WeakStress.projectedDivergence (WithLp.toLp 2 (fun j => toL2 (col j))) F := by
  rw [Leray.WeakStress.projectedDivergence_apply, Leray.WeakStress.divergence_apply,
    PiLp.inner_apply]
  simp only [lerayDivPairing, Leray.WeakStress.gradientCLM_apply,
    Leray.derivative_h1Projection, hF]

/-! ## Pairing integrands in similarity variables -/

/-- `⟨f, ψ⟩` at a spacetime point. -/
def pairTerm (f : ℝ → SpatialField) (ψ : SpaceTime → Space) (z : SpaceTime) : ℝ :=
  inner ℝ (f z.1 z.2) (ψ z)

/-- `⟨f, (y·∇)ψ⟩` at a spacetime point, `y = z.2`. -/
def dilationTerm (f : ℝ → SpatialField) (ψ : SpaceTime → Space) (z : SpaceTime) : ℝ :=
  inner ℝ (f z.1 z.2) (spatialDerivative ψ z.1 z.2 z.2)

/-- Two integrable spacetime integrands with equal integrals. -/
structure WeakIdentity (f g : SpaceTime → ℝ) : Prop where
  left_integrable : Integrable f
  right_integrable : Integrable g
  eq : ∫ z, f z = ∫ z, g z

/-! ## The heat profile `H_h[u_dss]` (lines 159–163, B0707) -/

/-- `H_h[u](y,τ) = e^{τ/2}[e^{h e^τ Δ} u](e^{τ/2} y)`, with the compiled Gaussian convolution
`Heat.average s u x = ∫ kernel s z • u (x - z) dz`, `kernel s = (4πs)^{-3/2} e^{-|x|²/4s}`. -/
def heatProfile (h : ℝ) (u : SpatialField) (τ : ℝ) (y : Space) : Space :=
  Real.exp (τ / 2) • Heat.average (h * Real.exp τ) u (Real.exp (τ / 2) • y)

theorem heatProfile_apply (h : ℝ) (u : SpatialField) (τ : ℝ) (y : Space) :
    heatProfile h u τ y = Real.exp (τ / 2) •
      ∫ z : Space, Heat.kernel (h * Real.exp τ) z • u (Real.exp (τ / 2) • y - z) := rfl

/-! ## The background equation `loc:eq:background` (lines 164–168, B0708) -/

/-- The linear part of `∂_τU = hΔU + ½y·∇U + ½U - 𝔓div(U⊗U)` tested against `ψ`:
`⟨U, ∂_τψ⟩ + h⟨U, Δψ⟩ - ⟨U, ψ⟩ - ½⟨U, (y·∇)ψ⟩`. The terms `-⟨U,ψ⟩ - ½⟨U,(y·∇)ψ⟩` are the
adjoint of `½ y·∇ + ½` on `ℝ³`. -/
def linearBackgroundIntegrand (h : ℝ) (U : ℝ → SpatialField) (ψ : SpaceTime → Space)
    (z : SpaceTime) : ℝ :=
  temporalTerm U ψ z + h * diffusionTerm U ψ z - pairTerm U ψ z -
    (1 / 2 : ℝ) * dilationTerm U ψ z

/-- `⟨𝔓 div(U(τ) ⊗ U(τ)), ψ(τ)⟩` at the phase `τ`. -/
def projectedConvection (U : ℝ → SpatialField) (ψ : SpaceTime → Space) (τ : ℝ) : ℝ :=
  lerayDivPairing (tensorColumns (U τ) (U τ)) (slice ψ τ)

/-- `U` is a distributional solution of `loc:eq:background` on `ℝ × ℝ³` with the literal
Leray projection: for every test `ψ`,
`∫∫ ⟨U,∂_τψ⟩ + h⟨U,Δψ⟩ - ⟨U,ψ⟩ - ½⟨U,(y·∇)ψ⟩ - ∫ ⟨𝔓div(U⊗U), ψ⟩ dτ = 0`. -/
structure SolvesSimilarityBackground (h : ℝ) (U : ℝ → SpatialField) : Prop where
  /-- The columns of `U(τ) ⊗ U(τ)` are in `L²` (true since `|U|² ≲ ⟨y⟩⁻² + |r_heat|²`). -/
  tensor_memL2 : ∀ τ, ColumnsL2 (tensorColumns (U τ) (U τ))
  temporal_integrable : ∀ ψ, IsSimilarityTest ψ → Integrable (temporalTerm U ψ)
  diffusion_integrable : ∀ ψ, IsSimilarityTest ψ → Integrable (diffusionTerm U ψ)
  pair_integrable : ∀ ψ, IsSimilarityTest ψ → Integrable (pairTerm U ψ)
  dilation_integrable : ∀ ψ, IsSimilarityTest ψ → Integrable (dilationTerm U ψ)
  convection_integrable : ∀ ψ, IsSimilarityTest ψ → Integrable (projectedConvection U ψ)
  identity : ∀ ψ, IsSimilarityTest ψ →
    (∫ z, linearBackgroundIntegrand h U ψ z) - (∫ τ, projectedConvection U ψ τ) = 0

/-! ## The periodic graph `𝒴_{2,div}` and `loc:eq:graph` (lines 136–147, 172–179, B0005) -/

/-- The period slab `(0,𝒯] × ℝ³`. -/
def periodSlab (period : ℝ) : Set SpaceTime := Ioc (0 : ℝ) period ×ˢ univ

/-- Membership of a `𝒯`-periodic field in `𝒴_{2,div} = L²([0,𝒯], dτ/𝒯; L²_div)`
(lines 136–141): periodic (a choice of representative on the circle), jointly measurable,
square integrable on one period, solenoidal at almost every phase. The weight `1/𝒯` does
not affect membership. -/
structure IsY2Div (period : ℝ) (f : ℝ → SpatialField) : Prop where
  periodic : Function.Periodic f period
  measurable : AEStronglyMeasurable (fun z : SpaceTime => f z.1 z.2) volume
  memL2 : MemLp (fun z : SpaceTime => f z.1 z.2) 2 (volume.restrict (periodSlab period))
  solenoidal : ∀ᵐ τ, IsSolenoidal (f τ)

/-- `∫∫ ⟨b, Δψ⟩ = ∫∫ ⟨lapB, ψ⟩`: `lapB` is the distributional Laplacian of `b`. -/
def laplacianPairing (b lapB : ℝ → SpatialField) (ψ : SpaceTime → Space) : Prop :=
  WeakIdentity (diffusionTerm b ψ) (pairTerm lapB ψ)

/-- The adjoint of `𝒯₀ = ∂_τ - ½ y·∇` on `ℝ × ℝ³`:
`⟨𝒯₀ b, ψ⟩ = -⟨b, ∂_τψ⟩ + (3/2)⟨b, ψ⟩ + ½⟨b, (y·∇)ψ⟩`. -/
def driftAdjointTerm (b : ℝ → SpatialField) (ψ : SpaceTime → Space) (z : SpaceTime) : ℝ :=
  -temporalTerm b ψ z + (3 / 2 : ℝ) * pairTerm b ψ z + (1 / 2 : ℝ) * dilationTerm b ψ z

/-- `driftB` is the distributional `(∂_τ - ½ y·∇) b`. -/
def driftPairing (b driftB : ℝ → SpatialField) (ψ : SpaceTime → Space) : Prop :=
  WeakIdentity (driftAdjointTerm b ψ) (pairTerm driftB ψ)

/-- `loc:eq:graph`: `b, hΔb, (∂_τ - ½y·∇)b ∈ 𝒴_{2,div}`. Since `h > 0`, `hΔb ∈ 𝒴₂` is the
same as `Δb ∈ 𝒴₂`. The separate terms `∂_τ b` and `y·∇ b` are not required to be functions
(lines 186–187). -/
structure InPeriodicGraph (period : ℝ) (b lapB driftB : ℝ → SpatialField) : Prop where
  value : IsY2Div period b
  laplacian : IsY2Div period lapB
  drift : IsY2Div period driftB
  laplacian_weak : ∀ ψ, IsSimilarityTest ψ → laplacianPairing b lapB ψ
  drift_weak : ∀ ψ, IsSimilarityTest ψ → driftPairing b driftB ψ

/-! ## The mode equation `loc:eq:mode` (lines 180–185, B1007) -/

/-- The linear part of `σb + 𝒯₀b - hΔb - ½b + 𝔓div(U⊗b + b⊗U) = 0` tested against `ψ`, with
`𝒯₀ b = driftB` and `Δ b = lapB`. -/
def linearModeIntegrand (h σ : ℝ) (b lapB driftB : ℝ → SpatialField) (ψ : SpaceTime → Space)
    (z : SpaceTime) : ℝ :=
  σ * pairTerm b ψ z + pairTerm driftB ψ z - h * pairTerm lapB ψ z -
    (1 / 2 : ℝ) * pairTerm b ψ z

/-- `⟨𝔓 div(U(τ) ⊗ b(τ) + b(τ) ⊗ U(τ)), ψ(τ)⟩` at the phase `τ`. -/
def projectedCoupling (U b : ℝ → SpatialField) (ψ : SpaceTime → Space) (τ : ℝ) : ℝ :=
  lerayDivPairing (symTensorColumns (U τ) (b τ)) (slice ψ τ)

/-- `loc:eq:mode` in distributions on `ℝ × ℝ³`, with the literal Leray projection. -/
structure SolvesModeEquation (h σ : ℝ) (U b lapB driftB : ℝ → SpatialField) : Prop where
  /-- The columns of `U ⊗ b + b ⊗ U` are in `L²` at almost every phase. -/
  tensor_memL2 : ∀ᵐ τ, ColumnsL2 (symTensorColumns (U τ) (b τ))
  value_integrable : ∀ ψ, IsSimilarityTest ψ → Integrable (pairTerm b ψ)
  laplacian_integrable : ∀ ψ, IsSimilarityTest ψ → Integrable (pairTerm lapB ψ)
  drift_integrable : ∀ ψ, IsSimilarityTest ψ → Integrable (pairTerm driftB ψ)
  coupling_integrable : ∀ ψ, IsSimilarityTest ψ → Integrable (projectedCoupling U b ψ)
  identity : ∀ ψ, IsSimilarityTest ψ →
    (∫ z, linearModeIntegrand h σ b lapB driftB ψ z) + (∫ τ, projectedCoupling U b ψ τ) = 0

/-! ## The data -/

/-- The background half of the data: `h, 𝒯, u_dss, U_*, r_heat`. -/
structure BackgroundCore where
  /-- The auxiliary viscosity `h` (line 151). -/
  h : ℝ
  /-- The period `𝒯` (line 151). -/
  period : ℝ
  /-- The DSS profile `u_dss` (line 151). -/
  udss : SpatialField
  /-- The periodic similarity background `U_*(y,τ) = Ustar τ y` (line 164). -/
  Ustar : ℝ → SpatialField
  /-- The heat remainder `r_heat ∈ C_per H²` (line 167), a path in the compiled `H²`. -/
  rheat : ℝ → SobolevGraph.H2

/-- The mode half of the data: `σ, b_*` and the two graph witnesses. -/
structure ModeCore where
  /-- The growth exponent `σ` (line 172). -/
  σ : ℝ
  /-- The growing Floquet mode `b_*(y,τ) = bstar τ y` (line 172). -/
  bstar : ℝ → SpatialField
  /-- The distributional `Δ b_*` (line 175), determined a.e. by `b_*`. -/
  lapB : ℝ → SpatialField
  /-- The distributional `(∂_τ - ½ y·∇) b_*` (line 176), determined a.e. by `b_*`. -/
  driftB : ℝ → SpatialField

/-- All objects named by `prop:unstable-background`. -/
structure BackgroundData extends BackgroundCore, ModeCore

/-! ## The package -/

/-- The background clauses of `prop:unstable-background` (lines 150–168, 188–189). -/
structure IsExactBackground (B : BackgroundCore) : Prop where
  /-- `h > 0` (line 151). -/
  h_pos : 0 < B.h
  /-- `𝒯 > 0` (line 151). -/
  period_pos : 0 < B.period
  /-- `u_dss` is smooth away from zero (line 152). -/
  udss_smooth : ContDiffOn ℝ ∞ B.udss {0}ᶜ
  /-- `u_dss` is solenoidal on `ℝ³`, distributionally across zero (line 152). -/
  udss_solenoidal : IsSolenoidal B.udss
  /-- `u_dss` is nonzero (line 152); equivalent to `¬ u_dss =ᵐ 0` by continuity off zero. -/
  udss_nonzero : ∃ x : Space, x ≠ 0 ∧ B.udss x ≠ 0
  /-- The DSS law `u_dss(e^{𝒯/2}x) = e^{-𝒯/2}u_dss(x)` (line 154), for `x ≠ 0`. -/
  udss_dss : ∀ x : Space, x ≠ 0 →
    B.udss (Real.exp (B.period / 2) • x) = Real.exp (-(B.period / 2)) • B.udss x
  /-- `|D^α u_dss(x)| ≤ C_α |x|^{-1-|α|}` for `x ≠ 0`, `|α| ≤ 4` (lines 155–156), for the
  operator norm of the `k`-th Fréchet derivative, written without division. -/
  udss_bounds : ∀ k : ℕ, k ≤ 4 → ∃ C : ℝ, ∀ x : Space, x ≠ 0 →
    ‖iteratedFDeriv ℝ k B.udss x‖ * ‖x‖ ^ (k + 1) ≤ C
  /-- `r_heat ∈ C_per H²` (line 167): continuous into `H²(ℝ³;ℝ³)` ... -/
  rheat_continuous : Continuous B.rheat
  /-- ... and `𝒯`-periodic. -/
  rheat_periodic : Function.Periodic B.rheat B.period
  /-- `U_* = H_h[u_dss] + r_heat` (line 167), a.e. in `y` at every phase. -/
  Ustar_decomposition : ∀ τ : ℝ, B.Ustar τ =ᵐ[volume]
    fun y => heatProfile B.h B.udss τ y + ((B.rheat τ).value : SpatialField) y
  /-- `U_*` is solenoidal (line 164). -/
  Ustar_solenoidal : ∀ τ : ℝ, IsSolenoidal (B.Ustar τ)
  /-- `U_*` is `𝒯`-periodic (line 164), as a field at each phase. -/
  Ustar_periodic : ∀ τ : ℝ, B.Ustar (τ + B.period) =ᵐ[volume] B.Ustar τ
  /-- `U_*` solves `loc:eq:background` in distributions (lines 164–167). -/
  Ustar_equation : SolvesSimilarityBackground B.h B.Ustar
  /-- `u_dss` is axisymmetric without swirl (lines 188–189). -/
  udss_symmetric : IsAxisymmetricNoSwirl B.udss
  /-- `U_*` is axisymmetric without swirl at every phase (lines 188–189). -/
  Ustar_symmetric : ∀ τ : ℝ, IsAxisymmetricNoSwirl (B.Ustar τ)

/-- The mode clauses of `prop:unstable-background` other than `0 < σ < 1/4`
(lines 172–189), on the background `B`. -/
structure IsGraphMode (B : BackgroundCore) (M : ModeCore) : Prop where
  /-- `loc:eq:graph` (lines 173–179), including `𝒯`-periodicity of `b_*` (line 172). -/
  graph : InPeriodicGraph B.period M.bstar M.lapB M.driftB
  /-- `b_*` is nonzero as an element of `𝒴₂` (line 172). -/
  bstar_nonzero :
    ¬ ((fun z : SpaceTime => M.bstar z.1 z.2) =ᵐ[volume.restrict (periodSlab B.period)] 0)
  /-- `loc:eq:mode` in distributions (lines 180–185). -/
  mode_equation : SolvesModeEquation B.h M.σ B.Ustar M.bstar M.lapB M.driftB
  /-- `b_*` is axisymmetric without swirl at almost every phase (lines 188–189). -/
  bstar_symmetric : ∀ᵐ τ, IsAxisymmetricNoSwirl (M.bstar τ)

/-- The mode clauses of `prop:unstable-background` (lines 172–189), on the background `B`. -/
structure IsGrowingMode (B : BackgroundCore) (M : ModeCore) : Prop extends IsGraphMode B M where
  /-- `0 < σ` (line 172). -/
  σ_pos : 0 < M.σ
  /-- `σ < 1/4` (line 172). -/
  σ_lt : M.σ < 1 / 4

/-- `prop:unstable-background`, lines 150–191: every clause, for one data record. -/
def IsUnstableBackground (D : BackgroundData) : Prop :=
  IsExactBackground D.toBackgroundCore ∧ IsGrowingMode D.toBackgroundCore D.toModeCore

theorem IsUnstableBackground.background {D : BackgroundData} (hD : IsUnstableBackground D) :
    IsExactBackground D.toBackgroundCore := hD.1

theorem IsUnstableBackground.mode {D : BackgroundData} (hD : IsUnstableBackground D) :
    IsGrowingMode D.toBackgroundCore D.toModeCore := hD.2

/-- Assembling the package from its two halves (the identification of lines 13734–13742). -/
theorem isUnstableBackground_mk (B : BackgroundCore) (M : ModeCore)
    (hB : IsExactBackground B) (hM : IsGrowingMode B M) :
    IsUnstableBackground { B, M with } := ⟨hB, hM⟩

theorem IsGraphMode.toGrowingMode {B : BackgroundCore} {M : ModeCore} (h : IsGraphMode B M)
    (h0 : 0 < M.σ) (h1 : M.σ < 1 / 4) : IsGrowingMode B M :=
  { h with σ_pos := h0, σ_lt := h1 }


/-! ## The heat integrals of the package converge (lines 155–163)

`heatProfile` is a Bochner integral, which would be the junk value `0` if the integrand were
not integrable. The derivative bound with `k = 0` and continuity off zero make every heat
integral of `u_dss` absolutely convergent, so `heatProfile B.h B.udss` is the manuscript's
`H_h[u_dss]`. This is proved, not assumed: the package has no integrability clause. -/

/-- A field continuous off zero with `|u(x)| ≤ C|x|^{-1}` has convergent heat integrals at
every point and every positive time. -/
theorem heat_integrable_of_inverse_bound {u : SpatialField}
    (hcont : ContinuousOn u {0}ᶜ) {C : ℝ} (hC : ∀ x : Space, x ≠ 0 → ‖u x‖ * ‖x‖ ≤ C)
    {s : ℝ} (hs : 0 < s) (x : Space) :
    Integrable (fun z : Space => Heat.kernel s z • u (x - z)) := by
  have hmeas : AEStronglyMeasurable u volume := by
    have h := hcont.aestronglyMeasurable (μ := volume) isOpen_compl_singleton.measurableSet
    rwa [restrict_compl_singleton] at h
  have hmp := Measure.measurePreserving_sub_left (volume : Measure Space) x
  suffices H : Integrable (fun y : Space => Heat.kernel s (x - y) • u y) by
    have h2 := hmp.integrable_comp_of_integrable H
    refine h2.congr (Eventually.of_forall fun z => ?_)
    simp only [Function.comp, sub_sub_cancel]
  have hC0 : 0 ≤ C := by
    have hv : (EuclideanSpace.single 0 1 : Space) ≠ 0 := by
      intro h
      have := congrArg (fun v : Space => v 0) h
      simp at this
    exact (mul_nonneg (norm_nonneg _) (norm_nonneg _)).trans (hC _ hv)
  have hkc : Continuous (fun y : Space => Heat.kernel s (x - y)) := by
    show Continuous (fun y : Space => Heat.Gaussian.kernel (4 * s) (x - y))
    exact (Heat.Gaussian.kernel_smooth (4 * s)).continuous.comp (continuous_const.sub continuous_id)
  have hN : ∀ y : Space, Heat.kernel s (x - y) ≤ Heat.Gaussian.normalization (4 * s) :=
    fun y => Heat.Gaussian.kernel_le_normalization (by positivity) _
  have hk0 : ∀ y : Space, 0 ≤ Heat.kernel s (x - y) := fun y => Heat.kernel_nonneg hs _
  have hfm : AEStronglyMeasurable (fun y : Space => Heat.kernel s (x - y) • u y) volume :=
    hkc.aestronglyMeasurable.smul hmeas
  have hdec : ∀ᵐ y ∂(volume : Measure Space), ‖u y‖ ≤ C * ‖y‖ ^ (-(1 : ℝ)) := by
    filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (0 : Space))] with y hy
    have hy0 : y ≠ 0 := hy
    have hpos : 0 < ‖y‖ := norm_pos_iff.mpr hy0
    rw [Real.rpow_neg_one, ← div_eq_mul_inv, le_div_iff₀ hpos]
    exact hC y hy0
  have hdim : Module.finrank ℝ Space = 3 := finrank_euclideanSpace_fin
  have hball : IntegrableOn u (ball (0 : Space) 1) volume :=
    integrableOn_ball_of_norm_le_rpow (by rw [hdim]; norm_num) (by rw [hdim]; norm_num)
      (ae_restrict_of_ae hdec) hmeas
  have h1 : IntegrableOn (fun y : Space => Heat.kernel s (x - y) • u y) (ball (0 : Space) 1) := by
    refine Integrable.mono' (hball.norm.const_mul (Heat.Gaussian.normalization (4 * s)))
      hfm.restrict (Eventually.of_forall fun y => ?_)
    rw [norm_smul, Real.norm_of_nonneg (hk0 y)]
    exact mul_le_mul_of_nonneg_right (hN y) (norm_nonneg _)
  have hkint : Integrable (fun y : Space => Heat.kernel s (x - y)) :=
    hmp.integrable_comp_of_integrable (Heat.kernel_integrable hs)
  have h2 : IntegrableOn (fun y : Space => Heat.kernel s (x - y) • u y) (ball (0 : Space) 1)ᶜ := by
    refine Integrable.mono' (hkint.const_mul C).integrableOn hfm.restrict ?_
    rw [ae_restrict_iff' measurableSet_ball.compl]
    filter_upwards [hdec] with y hy hyb
    have hy1 : 1 ≤ ‖y‖ := by simpa [mem_ball, dist_zero_right, not_lt] using hyb
    have hpos : 0 < ‖y‖ := lt_of_lt_of_le one_pos hy1
    rw [norm_smul, Real.norm_of_nonneg (hk0 y)]
    have hu : ‖u y‖ ≤ C := by
      refine hy.trans ?_
      rw [Real.rpow_neg_one]
      calc C * ‖y‖⁻¹ ≤ C * 1 := mul_le_mul_of_nonneg_left (inv_le_one_of_one_le₀ hy1) hC0
        _ = C := mul_one C
    calc Heat.kernel s (x - y) * ‖u y‖ ≤ Heat.kernel s (x - y) * C :=
          mul_le_mul_of_nonneg_left hu (hk0 y)
      _ = C * Heat.kernel s (x - y) := mul_comm _ _
  have := h1.union h2
  rwa [union_compl_self, integrableOn_univ] at this

/-- Every heat integral defining `H_h[u_dss]` converges, for a package background. -/
theorem IsExactBackground.heat_integrable {B : BackgroundCore} (hB : IsExactBackground B)
    {s : ℝ} (hs : 0 < s) (x : Space) :
    Integrable (fun z : Space => Heat.kernel s z • B.udss (x - z)) := by
  obtain ⟨C, hC⟩ := hB.udss_bounds 0 (by norm_num)
  refine heat_integrable_of_inverse_bound hB.udss_smooth.continuousOn (C := C)
    (fun y hy => ?_) hs x
  simpa [norm_iteratedFDeriv_zero] using hC y hy

end UnforcedLeray.Blueprint
