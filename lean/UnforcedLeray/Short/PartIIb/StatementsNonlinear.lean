import UnforcedLeray.Short.PartIIb.Defs
import UnforcedLeray.Short.PartIIb.StatementsFree
import UnforcedLeray.Short.PartIIb.StatementsMixed
import UnforcedLeray.Blueprint.Construction.Steps

/-!
# Part II-b, module `background/short-background.tex`, second half (SP 2345-2643): statements

The global operator comparison, the exact inverse, the nonlinear correction (contraction), the
strong regularity and the final background output. All statements are about the concrete
`Cons.C03.Concrete.Params` objects (train, `U_raw`, inlet columns, datum) and the concrete spaces
`Params.Z = X_{q₀} × ℝ²`, `Params.Y`.

## Quantifiers over the slow data

`Params` has two fields that the regime `BgRegime` does not constrain: the eigenprofile `p.mode`
(`q`; its periodized eigenstream defines the inlet `E_ε`, the columns `𝒞_ε, 𝒞_0`, the quadratic
inlet source and the datum, SP 2347-2383) and the terminal slow age `p.ageCut` (`Σ`, `H = Σ/ν`,
the age cutoff of the inlet). The inlet is linear in `p.mode` and depends on `Σ`, so every
statement that involves it fixes a growing eigenpair `Planar.IsGrowingEigenpair λ q` (the frozen
growing pair of Corollary `cor:short-seed-dilation`, SP 2048-2049) and a slow age `Σ` before its
constants, and assumes `p.mode = q`, `p.ageCut = Σ` (as `Sub/G4.lean` does). The source chooses
`Σ` large from `m` (SP 2337-2342, `short-bg:flat-inverse`), so `ExactInverse`, `BackgroundResult`
and `BackgroundOutput` provide a threshold `Σ₀` and hold for every `Σ ≥ Σ₀`;
`GlobalOperatorComparison`, `QuadraticFamily` and `StrongRegularity` hold for every `Σ > 0`.
`PhysicalRowReduction` and `RawResidualFamily` have uniform constants (`Θ`, `J` and their
constants do not involve the inlet, and `RawRel` involves only `U_raw`); `PhysicalRowReduction`
assumes `p.ν ≤ 1` and `Planar.IsGrowingEigenpair λ p.mode` after `C` so `p.Efun i` is smooth when
splitting `pairF` between `IsCop p Ce` and `OrdRel`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411
  UnforcedLeray.B0412

/-! ## The global operator comparison and the exact inverse -/

/-- **`short-bg:global-operator-comparison`** (SP 2430-2470, label at 2464, with `short-bg:affine` (2383),
`short-bg:strong-late-coeff` (2417) and the young/late splitting SP 2417-2463): there is a fixed `N`
such that for every `D > 0` and all `a, b > 0` (the window parameters `σ = ε^a`, `S = ε^{-b}`), and
every `d_±`, there are a constant and a degree with
`‖K_ε - K_0‖_{H_p→H_p} + ‖𝒞_ε - 𝒞_0‖ ≤ 𝒫_ν[ε^{a/2} + ε^{b/2} + ε + ε^{θ-N(a+b)} + e^{-D/ν}]`,
`θ = 2/539`. The operators `K_ε, 𝒞_ε, K_0, 𝒞_0` exist as bounded operators on all of `H_p`
(inputs of arbitrary age support). The comparison is asserted only for small `ν` (`p.ν ≤ ν₀`):
the source works in the small-`ν` regime (SP 2468-2472, "`MΔ_ν < 1/2` for small `ν`"), and the
graphs `bg:common-body-graph` (SP 1357) and `bg:profile-graph` (SP 1912-1938) need the period
`0 < P = 2εc ≤ 1`, which holds for small `ν` (`period_le_one_of`, `Compose.lean`).
`N` is fixed (it comes from the localized comparison, SP 2455-2463, and does not see the inlet);
the constants depend on the slow age `Σ = p.ageCut` and the growing eigenpair `q = p.mode`, since
`𝒞_ε - 𝒞_0 = εsr_ε` is linear in the eigenstream (SP 2370-2383, `short-bg:affine`). -/
def GlobalOperatorComparison : Prop :=
  ∃ N : ℕ, ∀ (Sig : ℝ) (lam : ℂ) (q : Blueprint.Planar.Profile), 0 < Sig →
    Blueprint.Planar.IsGrowingEigenpair lam q →
  ∀ D : ℝ, 0 < D → ∀ a b : ℝ, 0 < a → 0 < b → ∀ dm dp : ℝ, 0 < dm →
    ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < C ∧ 0 < ν₀ ∧
      ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig → p.mode = q →
      (∃ Ke Ce, IsKop p Ke ∧ IsCop p Ce) ∧
      ∀ (Ke K0 : HpR p.c →L[ℝ] HpR p.c) (Ce C0 : E2 →L[ℝ] HpR p.c),
        IsKop p Ke → IsK0op p K0 → IsCop p Ce → IsC0op p C0 →
          ‖Ke - K0‖ + ‖Ce - C0‖ ≤ C * (p.ν ^ k)⁻¹ *
            (p.ε ^ (a / 2) + p.ε ^ (b / 2) + p.ε + p.ε ^ ((2 / 539 : ℝ) - N * (a + b)) +
              Real.exp (-D / p.ν))

/-- **The physical normalization** (SP 2493-2504, "Returning to physical normalization"; with
`bg:common-body-graph`, `bg:graph-embeddings`): the lift `f ↦ F` between the body space
`Y = Params.Y` and `H_p` is an isometry up to the factor `s = (πR²)^{1/p}` (`J`), and the map
`Θ : (f, α) ↦ (w, A) = (N_v T_εf, R^{2/p}α) ∈ Z` has norm `≤ C s` (graph norm of the response);
if `(I + K_ε)f + 𝒞_εα = J g` then `(w, A)` solves the ordinary system
`A_0w + 𝔓B_{V_0}w + (A_0E_ε + 𝔓B_{V_0}E_ε)α = 𝔓 g` (`Params.OrdRel`). The factor `s` cancels:
"no additional power of `R` is lost". -/
def PhysicalRowReduction : Prop :=
  ∀ dm dp : ℝ, 0 < dm → ∃ C : ℝ, 0 < C ∧
    ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.period ≤ 1 → p.ν ≤ 1 →
    ∀ (lam : ℂ), Blueprint.Planar.IsGrowingEigenpair lam p.mode →
    ∀ (Ke : HpR p.c →L[ℝ] HpR p.c) (Ce : E2 →L[ℝ] HpR p.c), IsKop p Ke → IsCop p Ce →
      ∃ (Θ : RowSpace p.c →L[ℝ] p.Z) (J : p.Y →L[ℝ] HpR p.c),
        ‖Θ‖ ≤ C * (Real.pi * p.R ^ 2) ^ (1 / bgp) ∧
        ‖J‖ ≤ ((Real.pi * p.R ^ 2) ^ (1 / bgp))⁻¹ ∧
        (∀ f : p.Y, ∀ᵐ x : ℝ × Space, rep (f : Yq p.period q0E) x.1 x.2 =
          NvC p.R (toProf p.c (J f)) x) ∧
        ∀ (y : RowSpace p.c) (f : p.Y), rowOp Ke Ce y = J f →
          p.OrdRel (Θ y) (f : Yq p.period q0E)

/-- **`short-bg:exact-inverse`** (SP 2493-2504): for the growing eigenpair `q = p.mode` and every
fixed `m > 0` there is `Σ₀` such that for every slow age `Σ = p.ageCut ≥ Σ₀` the ordinary system
`A_0w + 𝔓B_{V_0}w + (A_0E_ε + 𝔓B_{V_0}E_ε)α = 𝔓f` has a bounded linear right inverse
`f ↦ (w, A)` on the body space with `‖w‖_{X_p} + R^{2/p}|α| ≤ 𝒫_νe^{m/ν}‖f‖_{Y_p}`. (`Σ₀`
comes from `FlatInverse` at the decreased `m`, SP 2465-2470, so it may depend on `d₋`.) -/
def ExactInverse : Prop :=
  ∀ (lam : ℂ) (q : Blueprint.Planar.Profile), Blueprint.Planar.IsGrowingEigenpair lam q →
  ∀ m : ℝ, 0 < m → ∀ dm dp : ℝ, 0 < dm → ∃ Sig₀ : ℝ, 0 < Sig₀ ∧ ∀ Sig : ℝ, Sig₀ ≤ Sig →
    ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < C ∧ 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig → p.mode = q →
      ∃ T : p.Y →L[ℝ] p.Z, (∀ f : p.Y, p.OrdRel (T f) (f : Yq p.period q0E)) ∧
        ‖T‖ ≤ C * (p.ν ^ k)⁻¹ * Real.exp (m / p.ν)

/-! ## The nonlinear correction -/

/-- **The quadratic estimates** (SP 2505-2518, by `bg:common-body-graph`--`bg:graph-embeddings` and
`short-bg:affine`): the polarized quadratic source of `w + E_εα` is a bounded bilinear map
`Z × Z → Y`, norm `≤ 𝒫_ν`. The form is quadratic in the inlet, hence in `p.mode`, so the constant
depends on the fixed slow age `Σ = p.ageCut` and growing eigenpair `q = p.mode`. -/
def QuadraticFamily : Prop :=
  ∀ (Sig : ℝ) (lam : ℂ) (q : Blueprint.Planar.Profile), 0 < Sig →
    Blueprint.Planar.IsGrowingEigenpair lam q →
  ∀ dm dp : ℝ, 0 < dm → ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < C ∧ 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig → p.mode = q →
      ∃ Q : p.Z →L[ℝ] p.Z →L[ℝ] p.Y, (∀ z z', p.QuadRel z z' (Q z z')) ∧
        ‖Q‖ ≤ C * (p.ν ^ k)⁻¹

/-- **The raw residual** (SP 2042-2046, Part I `sct:residual-bound`, used at SP 2510-2518): the projected
residual `𝔓F_R` lies in `Y` with `‖𝔓F_R‖_Y ≤ 𝒫_νε^{3/11}`. (Input from Part I.) -/
def RawResidualFamily : Prop :=
  ∀ dm dp : ℝ, 0 < dm → ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < C ∧ 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ →
      ∃ g : p.Y, p.RawRel g ∧ ‖g‖ ≤ C * (p.ν ^ k)⁻¹ * p.ε ^ (3 / 11 : ℝ)

/-- The projected equation `𝔓F_R + 𝓛z + 𝒬(z, z) = 0` for the state `z = (w, A)` (SP 2519-2524):
`A_0U + 𝔓(U·∇U) = 0` for `U = V_0 + E_εα + w`, in pairings with solenoidal phase tests. -/
def ProjectedEquation (p : Params) (z : p.Z) : Prop :=
  ∃ gF gL gQ : Yq p.period q0E, p.RawRel gF ∧ p.OrdRel z gL ∧ p.QuadRel z z gQ ∧
    gF + gL + gQ = 0

/-- **`short-bg:result`** (SP 2505-2524, label at 2519): for every fixed `m > 0` there is an exact solution
`z = (w, A)` of the projected equation with
`‖w‖_{X_p} + R^{8/11}|α| = ‖z‖_Z ≤ 𝒫_νe^{m/ν}ε^{3/11}`; consequently `|α| ≤ 𝒫_νe^{m/ν}ε`
(`coord z = ε^{8/11}A`). As for `ExactInverse`, this holds for the growing eigenpair `q = p.mode`
and every slow age `Σ = p.ageCut ≥ Σ₀`. -/
def BackgroundResult : Prop :=
  ∀ (lam : ℂ) (q : Blueprint.Planar.Profile), Blueprint.Planar.IsGrowingEigenpair lam q →
  ∀ m : ℝ, 0 < m → ∀ dm dp : ℝ, 0 < dm → ∃ Sig₀ : ℝ, 0 < Sig₀ ∧ ∀ Sig : ℝ, Sig₀ ≤ Sig →
    ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < C ∧ 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig → p.mode = q →
      ∃ z : p.Z, ProjectedEquation p z ∧
        ‖z‖ ≤ C * (p.ν ^ k)⁻¹ * Real.exp (m / p.ν) * p.ε ^ (3 / 11 : ℝ)

/-! ## Regularity, datum, heat remainder (SP 2525-2643) -/

/-- The background `U = U_raw + E_εα + w` of a state (SP 2519-2524). -/
def bgField (p : Params) (z : p.Z) : ℝ → SpatialField := fun τ y =>
  p.raw τ y + ∑ i : Fin 2, p.coord z i • p.inlet i τ y + p.corr z τ y

/-- **`short-bg:strong` and all spatial orders** (SP 2525-2562, label at 2541): every solution of the projected
equation in the contraction ball has the correction `w` and the inlet `E_εα` bounded in
`L^p`, `W^{1,∞}` by `𝒫_νe^{m/ν}ε^{3/11}`, and `U` is `P`-periodic, solenoidal, axisymmetric without
swirl and jointly smooth through the axis.

The range of `m`: the source runs the bootstrap only for the contraction ball of SP 2507-2512
(radius `2Mδ`, `δ = 𝒫_νε^{3/11}`, `M = 𝒫_νe^{m/ν}`, a contraction when `4𝒫_νM²δ < 1`, "after
decreasing `m` so `2m < 3d₋/11`", SP 2512). Hence the hypothesis `2m < 3d₋/11`: with
`ε = e^{-d/ν}`, `d ≥ d₋`, the ball radius `C₁ν^{-k₁}e^{m/ν}ε^{3/11}` is then `≤ C₁ν^{-k₁}e^{-m/ν}`,
small for small `ν`, so the quadratic term `w·∇w` of `A_0w = f - 𝔓(V·∇w + w·∇V + w·∇w)`
(SP 2525-2530) is dominated by the linear ones. The last conjunct is the `W^{1,∞}` bound of
`E_εα` (value and spatial derivative) in `short-bg:strong` (SP 2538-2541). The inlet bounds
`‖E_εα‖_{W^{j,∞}} ≤ 𝒫_{ν,j}|α|` (SP 2385-2387) are linear in the eigenstream, so the constants
depend on the fixed slow age `Σ = p.ageCut` and growing eigenpair `q = p.mode`; no inverse is
used (SP 2525), so every `Σ > 0` is allowed. -/
def StrongRegularity : Prop :=
  ∀ (Sig : ℝ) (lam : ℂ) (q : Blueprint.Planar.Profile), 0 < Sig →
    Blueprint.Planar.IsGrowingEigenpair lam q →
  ∀ m : ℝ, 0 < m → ∀ dm dp : ℝ, 0 < dm → 2 * m < 3 * dm / 11 → ∀ (C₁ : ℝ) (k₁ : ℕ), 0 < C₁ →
    ∃ (C₂ : ℝ) (k₂ : ℕ) (ν₀ : ℝ), 0 < C₂ ∧ 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig → p.mode = q →
      ∀ z : p.Z, ProjectedEquation p z →
      ‖z‖ ≤ C₁ * (p.ν ^ k₁)⁻¹ * Real.exp (m / p.ν) * p.ε ^ (3 / 11 : ℝ) →
      ContDiff ℝ ∞ (fun x : ℝ × Space => bgField p z x.1 x.2) ∧
      Function.Periodic (bgField p z) p.period ∧
      (∀ τ, IsSolenoidal (bgField p z τ)) ∧
      (∀ τ, IsAxisymmetricNoSwirl (bgField p z τ)) ∧
      (∀ τ y, ‖p.corr z τ y‖ ≤ C₂ * (p.ν ^ k₂)⁻¹ * Real.exp (m / p.ν) * p.ε ^ (3 / 11 : ℝ) ∧
        ‖fderiv ℝ (p.corr z τ) y‖ ≤ C₂ * (p.ν ^ k₂)⁻¹ * Real.exp (m / p.ν) * p.ε ^ (3 / 11 : ℝ)) ∧
      (∀ τ, eLpNorm (p.corr z τ) (ENNReal.ofReal bgp) volume ≤
        ENNReal.ofReal (C₂ * (p.ν ^ k₂)⁻¹ * Real.exp (m / p.ν) * p.ε ^ (3 / 11 : ℝ))) ∧
      (∀ τ y, ‖∑ i : Fin 2, p.coord z i • p.inlet i τ y‖ ≤ C₂ * (p.ν ^ k₂)⁻¹ *
          Real.exp (m / p.ν) * p.ε ^ (3 / 11 : ℝ) ∧
        ‖fderiv ℝ (fun y' => ∑ i : Fin 2, p.coord z i • p.inlet i τ y') y‖ ≤ C₂ * (p.ν ^ k₂)⁻¹ *
          Real.exp (m / p.ν) * p.ε ^ (3 / 11 : ℝ))

/-- **The final output of the background module** (SP 2563-2643, `short-bg:raw-heat` at 2601; the
interface used by Parts III-IV and by `Blueprint.IsB3ProjectedOutput`): at every parameter point
of the regime with `ν` small there are a state `z` and a heat remainder `Q ∈ C_per H²` such that
the datum `a = a_{α}` (nonzero, solenoidal, smooth off `0`, DSS with factor `e^{P/2}`,
`|D^ka| ≤ C|x|^{-1-k}` for `k ≤ 4`, axisymmetric without swirl), the background
`U = U_raw + E_εα + w` (periodic, solenoidal, symmetric, bounded with bounded gradient),
`Q = U - H_ν[a]` and the projected equation hold. The level carries the growing eigenpair
`q = p.mode` and a slow age `Σ = p.ageCut ≥ Σ₀` (`Σ₀` from `BackgroundResult`, SP 2337-2342). -/
def BackgroundOutput : Prop :=
  ∀ (lam : ℂ) (q : Blueprint.Planar.Profile), Blueprint.Planar.IsGrowingEigenpair lam q →
  ∀ dm dp : ℝ, 0 < dm → ∃ Sig₀ : ℝ, 0 < Sig₀ ∧ ∀ Sig : ℝ, Sig₀ ≤ Sig → ∃ ν₀ : ℝ, 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig → p.mode = q →
      ∃ (z : p.Z) (Q : ℝ → SobolevGraph.H2),
        Blueprint.IsB3ProjectedOutput p.ν p.period (p.datum (p.coord z)) (bgField p z) Q

end UnforcedLeray.Short.IIb
