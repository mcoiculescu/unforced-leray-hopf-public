import UnforcedLeray.Blueprint.Top
import UnforcedLeray.Blueprint.Construction.Cylinder
import Mathlib.Data.Real.Sign

/-!
# The construction of the package: steps C1–C9

`paper/main.tex`, completion of the construction (lines 13714–13745, blueprint B1033), and
the statements it combines:

| Step | Lines | Blueprint units | Content |
|---|---|---|---|
| C1 `StepReferenceChoice` | 691–800, 13208, 13608–13617 | B0085, B0882 | G1–G4 for the planar data; `σ₀ = μ₀ ∈ (1/16,1/8)`, `C₀ ≠ 0`; `𝓙` continuous at `σ₀` |
| C2 `StepPhaseLocked` | 13618–13626 | B0997 | the phase-locked sequence `ν_n ↓ 0` (t00763) |
| C3 `StepBackground` | 5093–5141, 13714–13725 | B0705 | Theorem B3 at `ν_n`, `P_n` (literal (2.5) with pressure) |
| C3′ `StepBackgroundProjected` | same | B0705 | alternative to C3 + C9: B3 with the projected equation (build-plan bypass §4.3) |
| C4 `StepGainTrace` | 13627–13651 | B0998, B0999 | `tr K₀(σ₀ + z/(2ℓ_n)) → e^{-z}` uniformly (t00764–t00765), for the explicit `K₀`; PROVED from C1, C2 (`stepGainTrace_of`) |
| C5 `StepGainBound` | 13658–13659 | B1000 | the explicit `K₀` is bounded on the window uniformly in `n`; PROVED from C1, C2 (`stepGainBound_of`) |
| C6 `StepUniformReturn` | 13377–13422, 13653–13660 | B0992, B1000 | `B_full G = I - K₀ + o(1)` on the window for a normalizer `G` with `det G ≠ 0` and `B_full G` continuous on the window (the manuscript's `G = G_H`) |
| C7 `StepReducedMatrix` | 9139–9232, 9738–9750, 10872–10900, 13240–13255, 13680–13692 | B1004 | the observation is admissible and `B_full(σ)` is the lower-right block of the inverse pencil on the window |
| C8 `StepPhysicalMode` | 10900–10911, 13693–13707 | B1005, B0773, B1006 | package-free: a nonzero zero-entrance lift on a bounded background is a graph mode (t00633, 13702) |
| C9 `PressureProjectionStep` | 107–110, 13719–13733 | B0708 (conversion) | package-free: (2.5) with an `L²` pressure gives the literal projected equation |

## What constrains the data

The objects are fields of one `ConstructionData`, indexed by the member `n` of the
phase-locked sequence. Each field is an explicit formula or is constrained by a
characterizing property that some step asserts; the property determines the field except
where noted:
* `planar` (`λ`, `q`, `q†`, `V_can`): `Planar.IsPlanarReference` in C1 (G1–G4). Then
  `γ = Re λ`, `ω = Im λ`, `κ = ⟨Dq,q†⟩`, `𝓛`, `𝓙`, `𝓒 = (63πi/128)𝓛𝓙` and `N_ν` are explicit
  definitions (`Construction/Planar.lean`); none is a free field.
* `ν`: the phase identity of C2.
* `U`, and with it `a`: constrained by Theorem B3's conclusions in C3 (or C3′), but NOT
  determined by them. Any exact `P_n`-periodic, `𝒪`-invariant similarity Navier–Stokes
  background with a nonzero DSS datum of factor `e^{P_n/2}` satisfies `IsB3Output`, provided
  it has bounded `U` and `∇U`, `Q = U - H_ν[a] ∈ C_per H²` and (2.5) with an `L²` pressure; a
  small-data DSS solution is an example. `Q` and `p` are then fixed by `U` and `a`. This is
  not exploitable: C6 and C7 are statements about the chosen `U_n`, any record meeting C3,
  C6 and C7 still yields a genuine `IsUnstableBackground` through the proved composition,
  and every step is true for the manuscript's train background.
* explicit: `ε_n` (t00764), `c_n`, `P_n`, `R_n`, `ℓ_n`, the window, `K₀`
  (`eq:m2-leading-return`), the prepared vorticity `φ_{ν,c} = P_c(N_νV_can(1/ν))`, its real
  inlet streams, and the inlet column `J^phys_σ = e^{νΔ}a` (`Construction/Cylinder.lean`).
* `observation`: the structural clauses of `prepared:p4.2`–`p4.3` in C7. The specific frozen
  tests are not pinned. Any admissible observation for which the pencil is invertible gives
  a reduced matrix whose kernel corresponds exactly to zero-entrance modes, so this freedom
  cannot make the composition easier; C6 must be proved for the observation chosen.
* `Bfull`: `IsReducedMatrix` in C7, which determines it uniquely given the observation.

The exact Gram matrix `G_H = C_HΦ_σ` is not a field: C6 asserts the existence of a
normalizer `G` with `det G ≠ 0` at each point of the window and `B_full G` continuous there
(continuity of `G` itself is not required), whose witness in the manuscript is `G_H`. The
argument uses `G_H` only as such a normalizer (lines 13653–13679). C6 for the pinned
`B_full` cannot be met by a choice of normalizer alone: with the explicit `K₀`, C4–C6 force
`det B_full` to vanish in the window.

C4 and C5 are proved from C1 and C2 in `Construction/Gain.lean`. All other steps are OPEN.
The compositions are in `Construction/Compose.lean`.
(The construction-step skeleton is adapted from `SkeletonDesignA/ConstructionSteps.lean`,
`SkeletonDesignB/ConstructionSteps.lean` and `SkeletonDesignC/ConstructionSteps.lean`.)
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Matrix
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Blueprint

open MatrixCrossing Planar

/-! ## Theorem B3 (lines 5093–5141) -/

/-- The pressure pairing `p div ψ`. -/
def pressureSimilarityTerm (p : ℝ → Space → ℝ) (ψ : SpaceTime → Space) (z : SpaceTime) : ℝ :=
  p z.1 z.2 * spatialDivergence ψ z.1 z.2

/-- `background:eq:2.5`: `∂_τU - νΔU - ½(y·∇U + U) + U·∇U + ∇p = 0` in distributions on
`ℝ × ℝ³`, tested against all similarity tests, each pairing convergent:
`∫∫ ⟨U,∂_τψ⟩ + ν⟨U,Δψ⟩ - ⟨U,ψ⟩ - ½⟨U,(y·∇)ψ⟩ + ⟨U, Dψ U⟩ + p div ψ = 0`. -/
structure SolvesSimilarityNSWithPressure (ν : ℝ) (U : ℝ → SpatialField)
    (p : ℝ → Space → ℝ) : Prop where
  temporal_integrable : ∀ ψ, IsSimilarityTest ψ → Integrable (temporalTerm U ψ)
  diffusion_integrable : ∀ ψ, IsSimilarityTest ψ → Integrable (diffusionTerm U ψ)
  pair_integrable : ∀ ψ, IsSimilarityTest ψ → Integrable (pairTerm U ψ)
  dilation_integrable : ∀ ψ, IsSimilarityTest ψ → Integrable (dilationTerm U ψ)
  convection_integrable : ∀ ψ, IsSimilarityTest ψ → Integrable (convectionTerm U ψ)
  pressure_integrable : ∀ ψ, IsSimilarityTest ψ → Integrable (pressureSimilarityTerm p ψ)
  identity : ∀ ψ, IsSimilarityTest ψ →
    ∫ z, (linearBackgroundIntegrand ν U ψ z + convectionTerm U ψ z +
      pressureSimilarityTerm p ψ z) = 0

/-- A background with bounded velocity and bounded spatial gradient (line 5122: "Every fixed
spatial derivative of `U` is bounded at fixed parameters"; lines 10901–10902: "the fixed actual
background has bounded `U, ∇U`"), jointly measurable. These are the background facts the
weak-to-body step C8 uses. -/
structure IsBoundedBackground (U : ℝ → SpatialField) : Prop where
  measurable : AEStronglyMeasurable (fun z : SpaceTime => U z.1 z.2) volume
  differentiable : ∀ τ, Differentiable ℝ (U τ)
  bounded : ∃ C : ℝ, ∀ τ y, ‖U τ y‖ ≤ C ∧ ‖fderiv ℝ (U τ) y‖ ≤ C

/-- The clauses of Theorem B3 that do not involve the pressure, at one viscosity, as used at
lines 13714–13742 and by C8: the datum `a` of (2.8) with the derivative orders the package
uses (`|α| ≤ 4`, lines 155–156), the periodic `𝒪`-invariant background (2.2), (2.4) with
bounded `U` and `∇U`, and `Q = U - H_ν[a] ∈ C_per H²` (2.10). The bounds (2.6)–(2.7) and the
trace (2.9) are used only inside C6 and C7. -/
structure IsB3Core (ν P : ℝ) (a : SpatialField) (U : ℝ → SpatialField)
    (Q : ℝ → SobolevGraph.H2) : Prop where
  datum_smooth : ContDiffOn ℝ ∞ a {0}ᶜ
  datum_solenoidal : IsSolenoidal a
  datum_nonzero : ∃ x : Space, x ≠ 0 ∧ a x ≠ 0
  datum_dss : ∀ x : Space, x ≠ 0 → a (Real.exp (P / 2) • x) = Real.exp (-(P / 2)) • a x
  datum_bounds : ∀ k : ℕ, k ≤ 4 → ∃ C : ℝ, ∀ x : Space, x ≠ 0 →
    ‖iteratedFDeriv ℝ k a x‖ * ‖x‖ ^ (k + 1) ≤ C
  datum_symmetric : IsAxisymmetricNoSwirl a
  background_bounded : IsBoundedBackground U
  background_periodic : Function.Periodic U P
  background_solenoidal : ∀ τ, IsSolenoidal (U τ)
  background_symmetric : ∀ τ, IsAxisymmetricNoSwirl (U τ)
  remainder : ∀ τ, ((Q τ).value : SpatialField) =ᵐ[volume] U τ - heatProfile ν a τ
  remainder_continuous : Continuous Q
  remainder_periodic : Function.Periodic Q P

/-- What Theorem B3 delivers, literally: the clauses of `IsB3Core` and the equation (2.5)
with its global pressure `p = ∑ R_iR_j(U_iU_j) ∈ L²` at every phase (so `U_iU_j ∈ L²`). -/
structure IsB3Output (ν P : ℝ) (a : SpatialField) (U : ℝ → SpatialField)
    (Q : ℝ → SobolevGraph.H2) (p : ℝ → Space → ℝ) : Prop extends IsB3Core ν P a U Q where
  equation : SolvesSimilarityNSWithPressure ν U p
  products_L2 : ∀ τ, ColumnsL2 (tensorColumns (U τ) (U τ))
  pressure_L2 : ∀ τ, MemLp (p τ) 2 volume

/-- The pressure-free form of Theorem B3's output (the bypass §4.3 of the build plan
`scoping/README.md`): the clauses of `IsB3Core` and the projected equation
`loc:eq:background` with the literal `𝔓`. It follows from `IsB3Output` and C9
(`IsB3Output.toProjected` in `Compose.lean`). -/
structure IsB3ProjectedOutput (ν P : ℝ) (a : SpatialField) (U : ℝ → SpatialField)
    (Q : ℝ → SobolevGraph.H2) : Prop extends IsB3Core ν P a U Q where
  projected_equation : SolvesSimilarityBackground ν U

/-! ## The construction data -/

/-- The objects of the completion section, indexed by the member `n` of the phase-locked
sequence (lines 13608–13745). See the module docstring for what constrains each field. -/
structure ConstructionData where
  /-- The planar reference data `λ, q, q†, V_can` (G1–G4). -/
  planar : PlanarData
  /-- `σ₀ = μ₀` (`eq:st18-t00755`). -/
  σ₀ : ℝ
  /-- The phase-locked viscosities `ν_n` (t00763). -/
  ν : ℕ → ℝ
  /-- The DSS datum `a` of Theorem B3 at `ν_n` (`background:eq:2.8`). -/
  a : ℕ → SpatialField
  /-- The exact background `U = U_raw + E_bg α_bg + w_bg` at `ν_n` (`background:eq:2.4`). -/
  U : ℕ → ℝ → SpatialField
  /-- `Q = U - H_ν[a] ∈ C_per H²` (`background:eq:2.10`). -/
  Q : ℕ → ℝ → SobolevGraph.H2
  /-- The global pressure `p = ∑ R_iR_j(U_iU_j)`. -/
  p : ℕ → ℝ → Space → ℝ
  /-- The fixed averaged terminal observation `C_H` at level `n` (`prepared:p4.3`). -/
  observation : ℕ → ObservationData
  /-- The full reduced matrix `B_full(σ)` (`eq:m4-inverse-blocks`, t00766). -/
  Bfull : ℕ → ℝ → Matrix2

namespace ConstructionData

variable (F : ConstructionData)

/-- `γ = Re λ` (`eq:st18-t00008`). -/
def growth : ℝ := F.planar.eigenvalue.re

/-- `ω = Im λ`. -/
def frequency : ℝ := F.planar.eigenvalue.im

/-- `κ = ℓ(Dq)`. -/
def κ : ℂ := F.planar.kappa

/-- `𝓒` (`eq:m2-signed-invariant`). -/
def coeff : ℝ → ℂ := F.planar.signedCoeff

/-- `C₀ = 𝒞(σ₀)` (line 13617). -/
def C₀ : ℂ := F.coeff F.σ₀

/-- `ε_n = (e^{-γ/ν_n} ν_n^{Re κ - 5 - 2σ₀} / (2|C₀|))^{1/3}` (`eq:st18-t00764`). -/
def amplitude (n : ℕ) : ℝ :=
  (Real.exp (-(F.growth / F.ν n)) * F.ν n ^ (F.κ.re - 5 - 2 * F.σ₀) / (2 * ‖F.C₀‖)) ^ (1 / 3 : ℝ)

/-- `c_n = ν_n^{-2}` (t00764). -/
def spacing (n : ℕ) : ℝ := (F.ν n ^ 2)⁻¹

/-- The period `P = 2εc` (line 13716). -/
def period (n : ℕ) : ℝ := 2 * F.amplitude n * F.spacing n

/-- The ring radius `R = ε⁻¹` (line 13716). -/
def radius (n : ℕ) : ℝ := (F.amplitude n)⁻¹

/-- `ℓ_n = |log ν_n|` (line 13633). -/
def ell (n : ℕ) : ℝ := |Real.log (F.ν n)|

/-- `σ₀ + z/(2ℓ_n)` (line 13634). -/
def point (n : ℕ) (z : ℝ) : ℝ := F.σ₀ + z / (2 * F.ell n)

/-- The window `|z| ≤ 1` (lines 13633–13651). -/
def window (n : ℕ) : Set ℝ := Icc (F.point n (-1)) (F.point n 1)

/-- `N_{ν_n} = e^{λ/ν_n}ν_n^{-κ}`. -/
def gauge (n : ℕ) : ℂ := F.planar.gaugeFactor (F.ν n)

/-- `ρ_{ν,ε}(σ) = ε³ν^{3+2σ}/c` (line 13148). -/
def returnScale (n : ℕ) (σ : ℝ) : ℝ := F.amplitude n ^ 3 * F.ν n ^ (3 + 2 * σ) / F.spacing n

/-- The first factor `-(63π/64)ρ(Re 𝓛, Im 𝓛)` of `K₀` (`eq:m2-leading-return`). -/
def gainA (n : ℕ) (σ : ℝ) : Vector2 :=
  ![-(63 * Real.pi / 64) * F.returnScale n σ * (F.planar.couplingL σ).re,
    -(63 * Real.pi / 64) * F.returnScale n σ * (F.planar.couplingL σ).im]

/-- The second factor `(Im[N_ν𝓙], Re[N_ν𝓙])` of `K₀` (`eq:m2-leading-return`). -/
def gainB (n : ℕ) (σ : ℝ) : Vector2 :=
  ![(F.gauge n * F.planar.mellinJ σ).im, (F.gauge n * F.planar.mellinJ σ).re]

/-- The leading rank-one return `K₀(σ)` in the real inlet basis `(2Reφ_{ν,c}, -2Imφ_{ν,c})`
(`eq:m2-leading-return`, line 13183). -/
def K0 (n : ℕ) (σ : ℝ) : Matrix2 := outerProduct (F.gainA n σ) (F.gainB n σ)

/-- The prepared planar vorticity profile `q_{1/ν} = e^{λ/ν}(1/ν)^κV_can(1/ν) = N_νV_can(1/ν)`
(`eq:st18-t00014`, `eq:m2-prepared-actual`). -/
def preparedProfile (n : ℕ) : Profile :=
  fun r => F.gauge n * F.planar.canonical (F.ν n)⁻¹ r

/-- The streams of the real inlet basis `(2Reφ_{ν,c}, -2Imφ_{ν,c})`, `φ_{ν,c} = P_cq_{1/ν}`
(lines 9145–9148, 13110). -/
def inletStreams (n : ℕ) : Fin 2 → ℝ × ℝ → ℝ :=
  ![fun x => 2 * (periodicStream (F.preparedProfile n) (F.spacing n) x).re,
    fun x => -2 * (periodicStream (F.preparedProfile n) (F.spacing n) x).im]

/-- The background half of the package at level `n`, identified as at line 13741:
`h = ν`, `𝒯 = P`, `u_dss = a`, `U_* = U`, `r_heat = Q`. -/
def backgroundCore (n : ℕ) : BackgroundCore :=
  ⟨F.ν n, F.period n, F.a n, F.U n, F.Q n⟩

end ConstructionData

/-! ## The steps -/

/-- **Step C1** `StepReferenceChoice`: the planar data satisfy G1–G4, with `-2 < ω < 0`
(`eq:st18-t00008`); `σ₀ = μ₀ ∈ (1/16,1/8)` with `C₀ = 𝒞(σ₀) ≠ 0` (`eq:st18-t00755`); and
`𝓙` is continuous at `σ₀` (G4: holomorphic on `Re μ > -3/2`). The continuity of `𝓛` is
proved (`PlanarData.continuousAt_couplingL`).
* Tex: lines 691–800 (G1–G4), 13208, 13217, 13608–13617.
* Units: B0085, B0882 (with the G1–G4 units of `sec:gaussian`).
* Infrastructure: the Gaussian growing pair (G1, INF10, INF12, INF18), the canonical branch
  (G3b), the couplings (G4, INF20). -/
def StepReferenceChoice (F : ConstructionData) : Prop :=
  IsPlanarReference F.planar ∧ F.frequency ∈ Ioo (-2 : ℝ) 0 ∧
    F.σ₀ ∈ Ioo (1 / 16 : ℝ) (1 / 8) ∧ F.C₀ ≠ 0 ∧ ContinuousAt F.planar.mellinJ F.σ₀

/-- **Step C2** `StepPhaseLocked` (`eq:st18-t00763`): `ν_n > 0`, `ν_n → 0`, and
`ω/ν_n - Im κ log ν_n + arg C₀ = 2π sign(ω) n` for all large `n`.
* Tex: lines 13618–13626.
* Units: B0997.
* Infrastructure: the intermediate value theorem for the phase (INF31). -/
def StepPhaseLocked (F : ConstructionData) : Prop :=
  (∀ n, 0 < F.ν n) ∧ Tendsto F.ν atTop (𝓝 0) ∧
    ∀ᶠ n : ℕ in atTop, F.frequency / F.ν n - F.κ.im * Real.log (F.ν n) + Complex.arg F.C₀ =
      2 * Real.pi * Real.sign F.frequency * n

/-- **Step C3** `StepBackground`: Theorem B3 at `ν = ν_n`, `P = P_n = 2ε_nc_n`, for all
large `n`.
* Tex: lines 5093–5141 (Theorem B3), 13714–13725.
* Units: B0705 (with B0186, B0685, B0687, B0701, B0704, B0725).
* Infrastructure: the whole background construction (Sections `sec:background`,
  `sec:mixed-background`): 2D Navier–Stokes on the periodic cylinder (INF16), parabolic
  maximal regularity (INF02), Calderón–Zygmund (INF01), cylinder analysis (INF13, INF23),
  Lemma 3-10's parameter choice. -/
def StepBackground (F : ConstructionData) : Prop :=
  ∀ᶠ n : ℕ in atTop, IsB3Output (F.ν n) (F.period n) (F.a n) (F.U n) (F.Q n) (F.p n)

/-- **Step C3′** `StepBackgroundProjected`: the pressure-free alternative to C3 (build-plan
bypass §4.3). Same tex lines, units and infrastructure as C3, without the global pressure.
`StepBackground` and C9 imply it (`StepBackground.toProjected`). -/
def StepBackgroundProjected (F : ConstructionData) : Prop :=
  ∀ᶠ n : ℕ in atTop, IsB3ProjectedOutput (F.ν n) (F.period n) (F.a n) (F.U n) (F.Q n)

/-- **Step C4** `StepGainTrace` (`eq:st18-t00764`–`eq:st18-t00765`): for the explicit `K₀`,
`tr K₀(σ₀ + z/(2ℓ_n)) = e^{-z} Re(𝒞(σ)/𝒞(σ₀)) → e^{-z}` uniformly for `|z| ≤ 1`.
* Tex: lines 13627–13651 (with `eq:st18-t00754`).
* Units: B0998, B0999.
* Infrastructure: algebra of `ε_n`, `N_ν` and the phase identity; continuity of `𝓒` at `σ₀`
  (C1 and the proved continuity of `𝓛`). No operator theory.
* Status: PROVED from C1 and C2 (`stepGainTrace_of`, `Construction/Gain.lean`). -/
def StepGainTrace (F : ConstructionData) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    |(F.K0 n (F.point n z)).trace - Real.exp (-z)| ≤ δ

/-- **Step C5** `StepGainBound` (lines 13658–13659: "The factors of the leading outer
product are bounded on `K`, and its gain is bounded by (t00765)"): the entries of the
explicit `K₀` are bounded on the window, uniformly in `n`.
* Tex: lines 13658–13659.
* Units: B1000.
* Infrastructure: `ρ|N_ν| = ν^{2(σ-σ₀)}/(2|C₀|) ≤ e/(2|C₀|)` on the window; continuity of
  `𝓛` and `𝓙` at `σ₀`. No operator theory.
* Status: PROVED from C1 and C2 (`stepGainBound_of`, `Construction/Gain.lean`). -/
def StepGainBound (F : ConstructionData) : Prop :=
  ∃ M : ℝ, ∀ᶠ n : ℕ in atTop, ∀ σ ∈ F.window n, ∀ i j, |F.K0 n σ i j| ≤ M

/-- **Step C6** `StepUniformReturn` (`prop:uniform-reduced-return`,
`eq:stage02-uniform-return`, `unlabeled:13653`): there is a normalizer `G` with
`det G ≠ 0` at each point of the window and `B_full G` continuous on the window (continuity
of `G` itself is not required), such that `B_full G = I - K₀ + o(1)` uniformly on the window
(entrywise, equivalent to any norm on `ℝ^{2×2}`). The weaker hypothesis on `G` is all that
`eventually_endpoint_signs` and `exists_interior_kernel_of_gram_crossing` use. In the manuscript
`G = G_H = C_HΦ_σ`, the exact Gram matrix (`eq:st18-t00749`), invertible by
`prepared:p4.10`–`p4.11` and continuous by Section `sec:st18-12938`.
* Tex: lines 13377–13422 (proof 13423–13606), 13653–13660, 9660–9686, 10913–10949.
* Units: B0992, B1000 (with B0603–B0605, B0885, B0887–B0889, B0993–B0995; critic §3).
* Infrastructure: the reduced-return estimates of Sections 9–14 (INF13, INF19, INF22,
  INF28, INF29). -/
def StepUniformReturn (F : ConstructionData) : Prop :=
  ∃ G : ℕ → ℝ → Matrix2,
    (∀ᶠ n : ℕ in atTop, ContinuousOn (fun σ => F.Bfull n σ * G n σ) (F.window n) ∧
      ∀ σ ∈ F.window n, (G n σ).det ≠ 0) ∧
    ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop, ∀ σ ∈ F.window n, ∀ i j,
      |(F.Bfull n σ * G n σ - (1 - F.K0 n σ)) i j| ≤ δ

/-- **Step C7** `StepReducedMatrix` (`eq:m4-inverse-blocks`, `eq:st18-t00631`–`t00632`): for
all large `n`, the observation is admissible and, on the whole window, `B_full(σ)` is the
full reduced matrix of the pencil on the background `U_n` with the explicit inlet column:
the pencil is injective and every observation is attained with inlet `B_fullβ`
(`IsReducedMatrix`). The exact correspondence of line 13681 then follows
(`IsReducedMatrix.zeroEntrance`, proved).
* Tex: lines 9738–9750, 9139–9232, 10872–10900, 13240–13255, 13680–13692.
* Units: B1004 (with B0770–B0772).
* Infrastructure: invertibility of the full pencil (the ordinary and gain inverse bounds of
  the common choice, `sec:operator`), the free stress inverse `𝒮_μ` (`sec:free-stress`),
  the inlet column (Lemma `lem:stress-setup:3.4`), uniqueness of the free problem in the
  periodic `H¹` class (INF13, INF19). -/
def StepReducedMatrix (F : ConstructionData) : Prop :=
  ∀ᶠ n : ℕ in atTop, IsAdmissibleObservation (F.spacing n) (F.observation n) ∧
    ∀ σ ∈ F.window n, IsReducedMatrix (F.ν n) (F.radius n) (F.period n) σ (F.U n)
      (F.inletStreams n) (F.observation n) (F.Bfull n σ)

/-- **Step C8** `StepPhysicalMode` (`eq:st18-t00633`, `unlabeled:13702`, `eq:st18-t00770`): a
general lemma, independent of the data. On a periodic solenoidal background with bounded `U`
and `∇U`, the lift `𝒩_v b` of a nonzero zero-entrance solution of the full problem, for
`0 < σ < 1/4`, is a graph mode: it lies in the original graph `loc:eq:graph`, solves
`loc:eq:mode` with the literal `𝔓`, and is axisymmetric without swirl. Proof route: the body
force `𝔓(U·∇w + w·∇U)` is in `𝒴₂`; the free body inverse (accretive, since
`σ + 𝒯₀ - hΔ - ½ = (σ + ¼) + (𝒯₀ - ¾) - hΔ` with `𝒯₀ - ¾` skew-adjoint, line 7710) and
uniqueness of the free problem in the `H¹` class put `w` in the graph; the lift formula
gives the symmetry. The `B` of `eq:st18-t00633` is read as `𝒯₀ = ∂_τ - y·∇/2` (lines
8852, 8943, 9232, 13734–13741); the manuscript also uses `B` for `𝒯₀ - ¾` (lines 3434,
7710, 8211), a notational ambiguity recorded in the report.
* Tex: lines 10900–10911, 13693–13707, 13726–13742; 7700–7720.
* Units: B1005, B0773, B1006.
* Infrastructure: the free body inverse on `𝒴₂` (`sec:free-stress`, INF13, INF25);
  `L²` products with bounded coefficients; `𝔓` self-adjoint (compiled). -/
def StepPhysicalMode : Prop :=
  ∀ (B : BackgroundCore) (R σ : ℝ) (b : CylinderField),
    0 < B.h → 0 < B.period → 0 < R → 0 < σ → σ < 1 / 4 →
    IsBoundedBackground B.Ustar → Function.Periodic B.Ustar B.period →
    (∀ τ, IsSolenoidal (B.Ustar τ)) →
    IsInletSolution B.h B.period σ B.Ustar (fun _ _ => 0) (cylinderLift R b) →
    ¬ ((fun z : SpaceTime => cylinderLift R b z.1 z.2) =ᵐ[volume.restrict
      (periodSlab B.period)] 0) →
    ∃ lapB driftB : ℝ → SpatialField, IsGraphMode B ⟨σ, cylinderLift R b, lapB, driftB⟩

/-- **Step C9** `PressureProjectionStep`: a general lemma, independent of the data. The
unprojected equation (2.5) with an `L²` pressure, for a background solenoidal at every phase
whose products are in `L²`, gives the literal projected equation `loc:eq:background`.
Proof route: test (2.5) on `η(τ)∇φ(y)` to get `-Δp = ∂_i∂_j(U_iU_j)` at almost every phase;
approximate `(I - 𝔓)ψ` in `H¹` by test gradients (`Leray.gradientClosure`,
`Leray.h1Projection`); this gives `∫ p div ψ = -∑_j ⟨(U⊗U)_{·j}, (I-𝔓)∂_jψ⟩`.
* Tex: lines 107–110, 164–167, 13719–13733.
* Units: B0708 (the conversion from B0705's (2.5)).
* Infrastructure: `H¹` closure of test gradients (INF06, compiled `GradientClosure`,
  `SobolevProjection`); `H²` density of tests (INF11); Fubini on `ℝ × ℝ³`; a countable dense
  family of tests (separability of `H²`). -/
def PressureProjectionStep : Prop :=
  ∀ (ν : ℝ) (U : ℝ → SpatialField) (p : ℝ → Space → ℝ),
    (∀ τ, IsSolenoidal (U τ)) → (∀ τ, ColumnsL2 (tensorColumns (U τ) (U τ))) →
      (∀ τ, MemLp (p τ) 2 volume) → SolvesSimilarityNSWithPressure ν U p →
        SolvesSimilarityBackground ν U

end UnforcedLeray.Blueprint
