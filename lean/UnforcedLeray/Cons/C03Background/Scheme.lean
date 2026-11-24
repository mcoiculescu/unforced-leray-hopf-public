import UnforcedLeray.Cons.C03Background.Contraction
import UnforcedLeray.Cons.C03Background.RawLift

/-!
# Theorem B3 at one parameter point, from its ingredients

`paper/main.tex`, Theorem B3 (`background:thm:B3`, lines 5093–5141, unit B0705) and its proof
(lines 5161–6003, Sections `sec:st18-6030`–`sec:st18-6701`). The proof outline of B0705:
"Bound the raw residual (2.15). Build the affine inlet and the terminal row ((2.26)–(2.30)).
Prove the ordinary augmented inverse (2.31) … Close the nonlinear problem by contraction (2.43)
and keep it in the symmetric class. Upgrade derivatives ((2.44)–(2.46)) and bootstrap
smoothness. Define the datum `a` and prove its trace (2.47)–(2.9). Identify the heat remainder
… (2.48)–(2.51), then recover the Riesz pressure."

## The frozen objects

`BackgroundScheme ν c` records the objects of that proof at viscosity `ν` and train period `c`
(ring radius `R = ε⁻¹` and period `P = 2εc` enter through the hypotheses):

| Field | Manuscript object | Lines, unit |
|---|---|---|
| `train` | the actual Gaussian cylinder train `(v, p, ψ)` | 2045–2057, 5199; B0140, B0141 |
| `raw` | `U_raw`, the smooth Cartesian extension of `√s[v₁e_r + (v₂ + εH)e_z]` | 2075–2077, 5200; B0186, B0189 |
| `inletProfile`, `inlet` | the frozen inlet columns `E_bg = E_ε` (cutoff stream lifts) | 5146–5160, 5282–5303; B0303, B0298 |
| `Z` | `X_{q₀} × ℝ²`, `‖(w,A)‖ = ‖w‖_X + |A|`, `A = R^{2/p}α` | 5086–5091, 5697–5698; B0412 |
| `Y` | the body source space `Y_{q₀}` | 136–147, 5085; B0005, B0411 |
| `inv` | the augmented inverse (2.31) at terminal value `β = 0` | 5161–5406; B0684 |
| `quad` | the polarized quadratic source of (2.42) | 5693–5713; B0458 |
| `rawResidual` | the projected raw residual `𝔓F_R` | 5197–5205; B0282 |
| `lin` | the ordinary operator `A₀w + 𝔓B_{U_raw}w + (A₀E_bg + 𝔓B_{U_raw}E_bg)α` | 5168–5176; B0684 |
| `pair` | body source ↦ its pairing with similarity tests | 164–168 |
| `sym` | the real symmetric class (2.2) inside `Z` | 5081–5084, 5725; B0416, B0688 |
| `corr`, `coord` | `z = (w, A) ↦ w_bg`, `↦ α_bg = R^{-2/p}A` | 5096–5099 |
| `datum` | `α ↦ a`, the common DSS datum with inlet adjustment `α` | 5123–5129, 5852–5870; B0687 |

The background of a state `z` is `U = U_raw + E_bg α + w` (`field`, (2.4)); the closure map
is `Φ(z) = inv(-(𝔓F_R + quad z z))` (`Contraction.lean`), and `IsFixed ρ z` says that `z` is a
fixed point in the symmetric class and in the ball of radius `ρ`.

## The named hypotheses (each a manuscript result)

* `RawLiftHyp` — `background:eq:2.15` with `eq:m3-ring-lift` (B0282, B0186, B0189, B0695):
  `U_raw` agrees off the axis with the lift of `b_raw`, is bounded with bounded gradient
  (`‖U_raw‖_{W^{2,∞}} ≤ P`), smooth through the axis, and solenoidal ("complete solenoidal
  lift", line 2072).
* `InletHyp` — `eq:m2-background-inlet`, `background:eq:2.26`–`2.28` (B0303, B0297–B0299):
  the inlet columns are cutoff stream lifts of `c`-periodic profiles, bounded with bounded
  gradient (`background:eq:2.7`), solenoidal.
* `InverseBoundHyp` — `background:eq:2.31` (B0684, with B0682, B0683): `‖inv‖ ≤ M`.
* `QuadraticBoundHyp` — `background:eq:2.42` (B0458): `‖quad‖ ≤ P`.
* `RawResidualHyp` — `background:eq:2.15` (B0282, B0200): `‖𝔓F_R‖_{Y_{q₀}} ≤ δ`.
* `SymmetricClassHyp` — `unlabeled:5725` with `background:eq:2.2` (B0688, B0416): `sym` is
  closed, contains `0`, and `Φ` maps its part in the ball into it. When `Z` is already
  restricted to the class (2.2), as at line 5210, it holds with `sym = univ`
  (`symmetricClassHyp_univ`).
* `CorrectionHyp` — `background:eq:2.3`, `2.7`, `2.44`–`2.46`, `unlabeled:5831`
  (B0412, B0692, B0689–B0691, B0695): at the fixed point, `w_bg` is a background piece
  (periodic, solenoidal, in the class (2.2), smooth with bounded `w` and `∇w`). It is the
  conjunction (`correctionHyp_of`) of `CorrectionClassHyp` ((2.3) with (2.2): `w_bg ∈ X_{q₀}`
  is periodic, solenoidal, `𝒪`-invariant; B0412, B0416, B0688) and `CorrectionBoundsHyp`
  ((2.7), (2.44)–(2.46), `unlabeled:5831`: smooth through the axis with bounded `w`, `∇w`;
  B0692, B0689–B0691, B0695).
* `ZeroResidualHyp` — `background:eq:2.5` in projected form (B0701, lines 5726–5727: "the
  projected equation has zero residual"): at the fixed point, `U` solves `loc:eq:background`.
  It is derived (`zeroResidualHyp_of_expansion`) from two finer ingredients:
  * `OrdinarySolveHyp` — `eq:m3-ordinary-system` (B0684): the augmented inverse solves the
    ordinary system, `𝓛(inv f) = f`;
  * `ResidualExpansionHyp` — `background:eq:2.44` with (2.15) (B0689, B0282, B0701): at the
    fixed point the weak projected residual of `U = U_raw + E_bgα + w` is the pairing of
    `𝔓F_R + 𝓛z + 𝒬(z,z)` with the test, and each pairing of the weak form converges.
* `PressureHyp` — `background:eq:2.5` with `unlabeled:5995` (B0701, B0700): at the fixed
  point, `U` solves (2.5) with a global `L²` pressure and `U_iU_j ∈ L²`. With the compiled C9
  (`Cons/C09PressureProjection.lean`) it implies `ZeroResidualHyp`
  (`zeroResidualHyp_of_pressureHyp` in the main file `Cons/C03Background.lean`, which also
  uses the solenoidality of the three pieces).
* `DatumHyp` — `background:eq:2.8` (B0687): at the fixed point, `a = datum(α_bg)` is smooth
  off `0`, divergence free off `0`, nonzero, DSS with factor `e^{P/2}`,
  `|D^ka| ≤ C|x|^{-1-k}` (`k ≤ 4`), axisymmetric without swirl. Solenoidality across `0` is
  proved from these (`IsB3DatumOffZero.toIsB3Datum`, by the compiled AX07
  `Axi.isSolenoidal_of_point_singularity`).
* `HeatRemainderHyp` — `background:eq:2.10` (B0704, B0703): at the fixed point,
  `U - H_ν[a] ∈ C_per H²`.

## Proved here

* `exists_isFixed`: the fixed point exists (B0685, B0688), from `InverseBoundHyp`,
  `QuadraticBoundHyp`, `RawResidualHyp`, `SymmetricClassHyp` and `4PM²δ < 1`
  (`exists_fixedPoint_closureMap`).
* `isBackgroundPiece_field`: `U = U_raw + E_bg α + w_bg` is a background piece (periodicity
  and symmetry of `U_raw` and `E_bg` from the ring lift, `Pieces.lean`, `RawLift.lean`).
* `b3Projected_of_scheme`: **Theorem B3 in projected form at one parameter point**, i.e.
  `IsB3ProjectedOutput ν (2εc) a U Q` for `a = datum(α_bg)`, `U` the background of the fixed
  point and `Q` its heat remainder.
* `b3_of_scheme`: the literal form `IsB3Output` (with the pressure) from `PressureHyp`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Cons.C03

open UnforcedLeray.Blueprint UnforcedLeray.Axi

/-- The frozen objects of the proof of Theorem B3 at viscosity `ν` and train period `c`
(see the module docstring for the manuscript object behind each field). -/
structure BackgroundScheme (ν c : ℝ) where
  /-- The actual Gaussian cylinder train `eq:m3-train` (B0140), with its decaying stream. -/
  train : B0140.TrainSol ν c
  /-- `U_raw`: the smooth Cartesian extension of the raw ring lift (lines 2077, 5200). -/
  raw : ℝ → SpatialField
  /-- The profiles of the two frozen inlet columns (`background:eq:2.27`). -/
  inletProfile : Fin 2 → ℝ × (ℝ × ℝ) → Merid
  /-- The frozen inlet columns `E_bg = E_ε` (`eq:m2-background-inlet`). -/
  inlet : Fin 2 → ℝ → SpatialField
  /-- The state space `Z = X_{q₀} × ℝ²` with `‖(w,A)‖ = ‖w‖_X + |A|` (line 5698). -/
  Z : Type
  [zNormed : NormedAddCommGroup Z]
  [zSpace : NormedSpace ℝ Z]
  [zComplete : CompleteSpace Z]
  /-- The body source space `Y_{q₀}`. -/
  Y : Type
  [yNormed : NormedAddCommGroup Y]
  [ySpace : NormedSpace ℝ Y]
  /-- The augmented inverse (2.31) at terminal value `β = 0`. -/
  inv : Y →L[ℝ] Z
  /-- The polarized quadratic source of (2.42). -/
  quad : Z →L[ℝ] Z →L[ℝ] Y
  /-- The projected raw residual `𝔓F_R` (2.15). -/
  rawResidual : Y
  /-- The ordinary operator `𝓛(w,α) = A₀w + 𝔓B_{U_raw}w + (A₀E_bg + 𝔓B_{U_raw}E_bg)α` of
  `eq:m3-ordinary-system` (lines 5170–5176), bounded from `Z` to `Y` (the free graph bounds
  (2.21) and "only its complete equation source belongs to the body space", line 5154). -/
  lin : Z →L[ℝ] Y
  /-- The action of a body source on similarity tests, `f ↦ (ψ ↦ -∫∫⟨f,ψ⟩)`. -/
  pair : Y →ₗ[ℝ] ((SpaceTime → Space) → ℝ)
  /-- The real symmetric class (2.2) in `Z`. -/
  sym : Set Z
  /-- The correction `w_bg` of a state `z = (w, A)`. -/
  corr : Z → ℝ → SpatialField
  /-- The inlet coordinates `α_bg = R^{-2/p}A` of a state `z = (w, A)`. -/
  coord : Z → Fin 2 → ℝ
  /-- The common DSS datum with inlet adjustment `α` (`background:eq:2.8`). -/
  datum : (Fin 2 → ℝ) → SpatialField

attribute [instance] BackgroundScheme.zNormed BackgroundScheme.zSpace
  BackgroundScheme.zComplete BackgroundScheme.yNormed BackgroundScheme.ySpace

namespace BackgroundScheme

variable {ν c : ℝ} (S : BackgroundScheme ν c)

/-- The closure map of `background:eq:2.43`. -/
def Φ (z : S.Z) : S.Z := closureMap S.inv S.quad S.rawResidual z

/-- The background `U = U_raw + E_bg α + w` of a state `z` (`background:eq:2.4`). -/
def field (z : S.Z) : ℝ → SpatialField :=
  S.raw + ∑ i : Fin 2, S.coord z i • S.inlet i + S.corr z

/-- `z` is a fixed point of the closure map in the symmetric class and in the ball of
radius `ρ` (line 5721: "contraction on the ball of radius `2Mδ`"). -/
def IsFixed (ρ : ℝ) (z : S.Z) : Prop := z ∈ S.sym ∧ ‖z‖ ≤ ρ ∧ S.Φ z = z

end BackgroundScheme

/-! ## The named hypotheses -/

section Hyps

variable {ν c : ℝ} (S : BackgroundScheme ν c)

/-- **`background:eq:2.15` with `eq:m3-ring-lift`** (lines 2070–2098, 5197–5205, 5831–5850;
units B0186, B0189, B0282, B0695). `U_raw` agrees off the axis with the ring lift of
`b_raw = (v₁, v₂ + εH)` of the actual train, radius `R = ε⁻¹`; it is jointly measurable,
smooth through the axis (here: differentiable at every phase), with `U_raw` and `∇U_raw`
bounded (`‖U_raw‖_{W^{2,∞}} ≤ P`, (2.15)); and it is solenoidal ("complete solenoidal lift",
line 2072; `div U = 0` in (2.5)). -/
structure RawLiftHyp (ε : ℝ) : Prop where
  lift : ∀ τ y, y ∉ axis → S.raw τ y = Nv ε⁻¹ (rawProfile ε S.train.v S.train.ψ) τ y
  bounded : IsBoundedBackground S.raw
  solenoidal : ∀ τ, IsSolenoidal (S.raw τ)

/-- **The frozen inlet columns** (`eq:m2-background-inlet`, `background:eq:2.26`–`2.28`;
lines 5146–5160, 5264–5333; units B0303, B0297, B0298, B0299). Each column `E_i` is the
cutoff stream lift of a profile that is `c`-periodic in `ξ` ("Periodizing the harmonic part",
line 5268), agrees off the axis with its ring lift (radius `R = ε⁻¹`), is jointly measurable,
smooth, with `E_i` and `∇E_i` bounded (`‖E_bgα‖_∞ + ‖∇E_bgα‖_∞` in (2.7)), and is
solenoidal (a stream lift with its axial completion, line 5151). -/
structure InletHyp (ε c : ℝ) : Prop where
  profile_periodic : ∀ i s, 0 < s → ∀ ξ η,
    S.inletProfile i (s, (ξ + c, η)) = S.inletProfile i (s, (ξ, η))
  lift : ∀ i τ y, y ∉ axis → S.inlet i τ y = Nv ε⁻¹ (S.inletProfile i) τ y
  bounded : ∀ i, IsBoundedBackground (S.inlet i)
  solenoidal : ∀ i τ, IsSolenoidal (S.inlet i τ)

/-- **The ordinary augmented inverse `background:eq:2.31`** at terminal value `β = 0`
(lines 5161–5406, 5670–5691; units B0684, B0682, B0683): `‖w‖_X + R^{2/p}|α| ≤ M‖f‖_Y`,
`M = P_νe^{m/ν}`. -/
def InverseBoundHyp (M : ℝ) : Prop := ‖S.inv‖ ≤ M

/-- **The quadratic estimates `background:eq:2.42`** (lines 5693–5713; unit B0458), with
"the polarized difference estimates have the same polynomial constant": `‖𝒬(z,z')‖_Y ≤
P‖z‖_Z‖z'‖_Z`. -/
def QuadraticBoundHyp (P : ℝ) : Prop := ‖S.quad‖ ≤ P

/-- **The raw residual bound `background:eq:2.15`** (lines 5197–5205; units B0282, B0200):
`‖𝔓F_R‖_{Y_{q₀}} ≤ δ = P_νε^{3/11}`. -/
def RawResidualHyp (δ : ℝ) : Prop := ‖S.rawResidual‖ ≤ δ

/-- **The symmetric class `background:eq:2.2` is invariant** (`unlabeled:5725`, lines
5725–5727; units B0688, B0416): "The free operators, the Leray projection and the products
commute with `𝒪`, and `U_raw` and the inlet columns lie in (2.2); iteration from zero
therefore stays in the real class (2.2)." -/
def SymmetricClassHyp (ρ : ℝ) : Prop :=
  IsClosed S.sym ∧ (0 : S.Z) ∈ S.sym ∧ ∀ z ∈ S.sym, ‖z‖ ≤ ρ → S.Φ z ∈ S.sym

/-- With `Z` restricted to the class (2.2) from the start (line 5210: "with its sum graph norm
and the symmetry (2.2)"), the symmetric class is all of `Z`. -/
theorem symmetricClassHyp_univ (hsym : S.sym = univ) (ρ : ℝ) : SymmetricClassHyp S ρ := by
  rw [SymmetricClassHyp, hsym]
  exact ⟨isClosed_univ, mem_univ _, fun _ _ _ => mem_univ _⟩

/-- **The correction `w_bg`** (`background:eq:2.3`, `2.7`, `2.44`–`2.46`, `unlabeled:5831`;
lines 5085–5091, 5115–5122, 5729–5850; units B0412, B0692, B0689, B0690, B0691, B0695): at the
fixed point, `w_bg ∈ X_{q₀}` (periodic, solenoidal, in the class (2.2)) is jointly smooth,
with `‖w_bg‖_∞ + ‖∇w_bg‖_∞` bounded. -/
def CorrectionHyp (P ρ : ℝ) : Prop :=
  ∀ z, S.IsFixed ρ z → IsBackgroundPiece P (S.corr z)

/-- **`w_bg` lies in `X_{q₀}` with the symmetry (2.2)** (`background:eq:2.3`, lines 5085–5091,
5208–5210 "with … the symmetry (2.2)", 5725–5727; units B0412, B0416, B0688): at the fixed
point, `w_bg` is `P`-periodic, solenoidal and axisymmetric without swirl at every phase (for
its smooth representative, `unlabeled:5831`). -/
def CorrectionClassHyp (P ρ : ℝ) : Prop :=
  ∀ z, S.IsFixed ρ z → Function.Periodic (S.corr z) P ∧
    (∀ τ, IsSolenoidal (S.corr z τ)) ∧ ∀ τ, IsAxisymmetricNoSwirl (S.corr z τ)

/-- **The derivative upgrade and smoothness of `w_bg`** (`background:eq:2.7`, `2.44`–`2.46`,
`unlabeled:5831`; lines 5115–5122, 5729–5850; units B0692, B0689, B0690, B0691, B0695): at the
fixed point, `w_bg` is jointly measurable, smooth through the axis, with `‖w_bg‖_∞` and
`‖∇w_bg‖_∞` finite (`≤ P_νe^{m/ν}ε^{3/11}`). -/
def CorrectionBoundsHyp (ρ : ℝ) : Prop :=
  ∀ z, S.IsFixed ρ z → IsBoundedBackground (S.corr z)

theorem correctionHyp_of {P ρ : ℝ} (hcl : CorrectionClassHyp S P ρ)
    (hb : CorrectionBoundsHyp S ρ) : CorrectionHyp S P ρ := fun z hz =>
  { bounded := hb z hz
    periodic := (hcl z hz).1
    solenoidal := (hcl z hz).2.1
    symmetric := (hcl z hz).2.2 }

/-- **The ordinary inverse solves the ordinary system** (`eq:m3-ordinary-system`, lines
5168–5176, and (2.31)–(2.32), lines 5383–5398; unit B0684): at terminal value `β = 0`,
`𝓛(inv f) = f` for every body source `f`. -/
def OrdinarySolveHyp : Prop := ∀ f : S.Y, S.lin (S.inv f) = f

/-- The weak projected residual of `U` at the test `ψ`: the left side of the identity of
`SolvesSimilarityBackground`, `∫∫ ⟨U,∂_τψ⟩ + ν⟨U,Δψ⟩ - ⟨U,ψ⟩ - ½⟨U,(y·∇)ψ⟩ - ∫⟨𝔓div(U⊗U),ψ⟩`
(`loc:eq:background`, lines 164–168). -/
def weakResidual (ν : ℝ) (U : ℝ → SpatialField) (ψ : SpaceTime → Space) : ℝ :=
  (∫ z, linearBackgroundIntegrand ν U ψ z) - ∫ τ, projectedConvection U ψ τ

/-- The convergence clauses of `SolvesSimilarityBackground` (every pairing of the weak form
converges and `U ⊗ U` has `L²` columns), without the identity. -/
structure HasWeakForm (U : ℝ → SpatialField) : Prop where
  tensor_memL2 : ∀ τ, ColumnsL2 (tensorColumns (U τ) (U τ))
  temporal_integrable : ∀ ψ, IsSimilarityTest ψ → Integrable (temporalTerm U ψ)
  diffusion_integrable : ∀ ψ, IsSimilarityTest ψ → Integrable (diffusionTerm U ψ)
  pair_integrable : ∀ ψ, IsSimilarityTest ψ → Integrable (pairTerm U ψ)
  dilation_integrable : ∀ ψ, IsSimilarityTest ψ → Integrable (dilationTerm U ψ)
  convection_integrable : ∀ ψ, IsSimilarityTest ψ → Integrable (projectedConvection U ψ)

/-- **The residual expansion** (`background:eq:2.44` with `background:eq:2.15`, lines
5197–5205, 5729–5749; units B0689, B0282, B0701): at the fixed point `z = (w, A)`, every
pairing of the weak form of `loc:eq:background` converges for `U = U_raw + E_bgα + w`, and its
weak projected residual is the pairing of `𝔓F_R + 𝓛z + 𝒬(z,z)` with the test: the projected
Navier–Stokes residual of `U` is the raw residual, plus the ordinary operator applied to
`(w, α)` (all linear inlet terms), plus the quadratic terms `𝔓(e·∇e + e·∇w + w·∇e + w·∇w)`,
`e = E_bgα` ("All linear and quadratic inlet terms are included", line 5726). -/
def ResidualExpansionHyp (ρ : ℝ) : Prop :=
  ∀ z, S.IsFixed ρ z → HasWeakForm (S.field z) ∧ ∀ ψ, IsSimilarityTest ψ →
    weakResidual ν (S.field z) ψ = S.pair (S.rawResidual + S.lin z + S.quad z z) ψ


/-- **Zero projected residual** (`background:eq:2.5`, lines 5726–5727; unit B0701): "All
linear and quadratic inlet terms are included, so the projected equation has zero residual."
At the fixed point, `U` solves `loc:eq:background` with the literal `𝔓`. -/
def ZeroResidualHyp (ρ : ℝ) : Prop :=
  ∀ z, S.IsFixed ρ z → SolvesSimilarityBackground ν (S.field z)

/-- **`background:eq:2.5` with the global pressure** (lines 5101–5104, 5727–5728, 5995–5998;
units B0701, B0700): at the fixed point, `U` solves (2.5) with the Riesz pressure
`p = ∑R_iR_j(U_iU_j) ∈ C_per L²`, and `U_iU_j ∈ L²`. -/
def PressureHyp (ρ : ℝ) : Prop :=
  ∀ z, S.IsFixed ρ z → ∃ p : ℝ → Space → ℝ,
    SolvesSimilarityNSWithPressure ν (S.field z) p ∧
      (∀ τ, ColumnsL2 (tensorColumns (S.field z τ) (S.field z τ))) ∧
        ∀ τ, MemLp (p τ) 2 volume

/-- The datum clauses of Theorem B3 (`background:eq:2.8`, with the derivative orders
`k ≤ 4` that the package uses, lines 155–156), as in `Blueprint.IsB3Core`. -/
structure IsB3Datum (P : ℝ) (a : SpatialField) : Prop where
  smooth : ContDiffOn ℝ ∞ a {0}ᶜ
  solenoidal : IsSolenoidal a
  nonzero : ∃ x : Space, x ≠ 0 ∧ a x ≠ 0
  dss : ∀ x : Space, x ≠ 0 → a (Real.exp (P / 2) • x) = Real.exp (-(P / 2)) • a x
  bounds : ∀ k : ℕ, k ≤ 4 → ∃ C : ℝ, ∀ x : Space, x ≠ 0 →
    ‖iteratedFDeriv ℝ k a x‖ * ‖x‖ ^ (k + 1) ≤ C
  symmetric : IsAxisymmetricNoSwirl a

/-- The datum clauses with the divergence taken pointwise off the origin, as the stream
formula gives it (lines 5855–5866). Solenoidality on all of `ℝ³` is then proved
(`IsB3DatumOffZero.toIsB3Datum`): "At zero the omitted spherical divergence flux is `O(r)`, so
the field is globally solenoidal distributionally" (lines 5863–5865), which is the compiled
`Axi.isSolenoidal_of_point_singularity` (`Lib/AxisymmetricB/AxisRegularity.lean`, AX07). -/
structure IsB3DatumOffZero (P : ℝ) (a : SpatialField) : Prop where
  smooth : ContDiffOn ℝ ∞ a {0}ᶜ
  div_free : ∀ x : Space, x ≠ 0 → divergence a x = 0
  nonzero : ∃ x : Space, x ≠ 0 ∧ a x ≠ 0
  dss : ∀ x : Space, x ≠ 0 → a (Real.exp (P / 2) • x) = Real.exp (-(P / 2)) • a x
  bounds : ∀ k : ℕ, k ≤ 4 → ∃ C : ℝ, ∀ x : Space, x ≠ 0 →
    ‖iteratedFDeriv ℝ k a x‖ * ‖x‖ ^ (k + 1) ≤ C
  symmetric : IsAxisymmetricNoSwirl a

/-- The datum is globally solenoidal: `C¹` and divergence free off `0` with `|a| ≤ C|x|⁻¹`
(the case `k = 0` of the bounds) gives `IsSolenoidal a` (unit B0687, lines 5863–5865). -/
theorem IsB3DatumOffZero.toIsB3Datum {P : ℝ} {a : SpatialField} (h : IsB3DatumOffZero P a) :
    IsB3Datum P a := by
  obtain ⟨C, hC⟩ := h.bounds 0 (Nat.zero_le _)
  have hbd : ∀ x ≠ (0 : Space), ‖a x‖ ≤ C * ‖x‖⁻¹ := by
    intro x hx
    have h0 := hC x hx
    rw [norm_iteratedFDeriv_zero, zero_add, pow_one] at h0
    exact (le_mul_inv_iff₀ (norm_pos_iff.mpr hx)).mpr h0
  exact
    { smooth := h.smooth
      solenoidal := isSolenoidal_of_point_singularity (h.smooth.of_le (by simp)) h.div_free hbd
      nonzero := h.nonzero
      dss := h.dss
      bounds := h.bounds
      symmetric := h.symmetric }

/-- **The common DSS datum `background:eq:2.8`** (lines 5123–5129, 5852–5870; unit B0687):
at the fixed point, `a = datum(α_bg)` (the raw Gaussian inlet stream plus the entrance
adjustment of (2.27)) is smooth off `0`, divergence free off `0`, nonzero ("the finite inlet
perturbation [is] exponentially small" on the core, by (2.6)), DSS with factor `e^{P/2}`,
with `|D^ka| ≤ C_k|x|^{-1-k}`, and axisymmetric without swirl ((2.27)). -/
def DatumHyp (P ρ : ℝ) : Prop :=
  ∀ z, S.IsFixed ρ z → IsB3DatumOffZero P (S.datum (S.coord z))

/-- **The heat remainder `background:eq:2.10`** (lines 5134–5137, 5909–5993; units B0704,
B0703): at the fixed point, `Q := U - H_ν[a] ∈ C_per H²`, with `a = datum(α_bg)`. -/
def HeatRemainderHyp (P ρ : ℝ) : Prop :=
  ∀ z, S.IsFixed ρ z → ∃ Q : ℝ → SobolevGraph.H2, Continuous Q ∧ Function.Periodic Q P ∧
    ∀ τ, ((Q τ).value : SpatialField) =ᵐ[volume]
      S.field z τ - heatProfile ν (S.datum (S.coord z)) τ

/-- **Zero projected residual from the fixed point** (lines 5714–5727, unit B0701): the fixed
point solves `𝓛z = -(𝔓F_R + 𝒬(z,z))` (`OrdinarySolveHyp`), so the expanded residual vanishes. -/
theorem zeroResidualHyp_of_expansion {ρ : ℝ} (hsolve : OrdinarySolveHyp S)
    (hexp : ResidualExpansionHyp S ρ) : ZeroResidualHyp S ρ := by
  intro z hz
  obtain ⟨hw, hres⟩ := hexp z hz
  have hlin : S.lin z = -(S.rawResidual + S.quad z z) := by
    have h := hsolve (-(S.rawResidual + S.quad z z))
    have hfix : S.inv (-(S.rawResidual + S.quad z z)) = z := hz.2.2
    rw [hfix] at h
    exact h
  have hzero : S.rawResidual + S.lin z + S.quad z z = 0 := by
    rw [hlin]; abel
  exact
    { tensor_memL2 := hw.tensor_memL2
      temporal_integrable := hw.temporal_integrable
      diffusion_integrable := hw.diffusion_integrable
      pair_integrable := hw.pair_integrable
      dilation_integrable := hw.dilation_integrable
      convection_integrable := hw.convection_integrable
      identity := fun ψ hψ => by
        have h := hres ψ hψ
        rw [hzero, map_zero] at h
        exact h }

end Hyps

/-! ## The assembly -/

namespace BackgroundScheme

variable {ν c : ℝ} (S : BackgroundScheme ν c)

/-- **`background:eq:2.43` with `unlabeled:5725`** (B0685, B0688): with `4PM²δ < 1` the closure
map has a fixed point in the symmetric class in the ball of radius `2Mδ` (the reference form
of (2.4)–(2.6)), unique in that ball. -/
theorem exists_isFixed {M Pq δ : ℝ} (hinv : InverseBoundHyp S M) (hq : QuadraticBoundHyp S Pq)
    (hF : RawResidualHyp S δ) (hsmall : 4 * Pq * M ^ 2 * δ < 1)
    (hsym : SymmetricClassHyp S (2 * M * δ)) :
    ∃ z, S.IsFixed (2 * M * δ) z ∧ ∀ z' : S.Z, ‖z'‖ ≤ 2 * M * δ → S.Φ z' = z' → z' = z := by
  obtain ⟨hcl, h0, hmaps⟩ := hsym
  obtain ⟨z, hzS, hzρ, hfix, huniq⟩ :=
    exists_fixedPoint_closureMap S.inv S.quad S.rawResidual hinv hq hF hsmall hcl h0 hmaps
  exact ⟨z, ⟨hzS, hzρ, hfix⟩, huniq⟩

/-- `U = U_raw + E_bg α + w_bg` is a background piece of period `P = 2εc` at the fixed point. -/
theorem isBackgroundPiece_field {ε ρ : ℝ} (hε : ε ≠ 0) (hraw : RawLiftHyp S ε)
    (hin : InletHyp S ε c) (hcorr : CorrectionHyp S (2 * ε * c) ρ) {z : S.Z}
    (hz : S.IsFixed ρ z) : IsBackgroundPiece (2 * ε * c) (S.field z) := by
  have hR : ε⁻¹ ≠ 0 := inv_ne_zero hε
  have hP : 2 * ε * c = 2 * c / ε⁻¹ := by rw [div_inv_eq_mul]; ring
  have hr : IsBackgroundPiece (2 * ε * c) S.raw :=
    isBackgroundPiece_raw hε S.train hraw.lift hraw.bounded hraw.solenoidal
  have hE : ∀ i, IsBackgroundPiece (2 * ε * c) (S.inlet i) := fun i =>
    isBackgroundPiece_of_lift hR hP (hin.profile_periodic i) (hin.lift i) (hin.bounded i)
      (hin.solenoidal i)
  exact (hr.add (IsBackgroundPiece.lin2 hE (S.coord z))).add (hcorr z hz)

/-- The pressure-free clauses of Theorem B3 at the fixed point. -/
theorem isB3Core_field {ε ρ : ℝ} (hε : ε ≠ 0) (hraw : RawLiftHyp S ε)
    (hin : InletHyp S ε c) (hcorr : CorrectionHyp S (2 * ε * c) ρ)
    (hdat : DatumHyp S (2 * ε * c) ρ) {z : S.Z} (hz : S.IsFixed ρ z)
    {Q : ℝ → SobolevGraph.H2} (hQc : Continuous Q) (hQp : Function.Periodic Q (2 * ε * c))
    (hQ : ∀ τ, ((Q τ).value : SpatialField) =ᵐ[volume]
      S.field z τ - heatProfile ν (S.datum (S.coord z)) τ) :
    IsB3Core ν (2 * ε * c) (S.datum (S.coord z)) (S.field z) Q := by
  have hU := S.isBackgroundPiece_field hε hraw hin hcorr hz
  have ha := (hdat z hz).toIsB3Datum
  exact
    { datum_smooth := ha.smooth
      datum_solenoidal := ha.solenoidal
      datum_nonzero := ha.nonzero
      datum_dss := ha.dss
      datum_bounds := ha.bounds
      datum_symmetric := ha.symmetric
      background_bounded := hU.bounded
      background_periodic := hU.periodic
      background_solenoidal := hU.solenoidal
      background_symmetric := hU.symmetric
      remainder := hQ
      remainder_continuous := hQc
      remainder_periodic := hQp }

/-- **Theorem B3 in projected form at one parameter point** (`background:thm:B3`, lines
5093–5141, unit B0705): from the named ingredients and the scalar condition `4PM²δ < 1` of
(2.43), there are `a`, `U`, `Q` with `IsB3ProjectedOutput ν (2εc) a U Q`. The witnesses are
`a = datum(α_bg)`, `U = U_raw + E_bgα_bg + w_bg` for the fixed point `(w_bg, α_bg)` of the
closure map, and the heat remainder `Q`. -/
theorem b3Projected_of_scheme {ε M Pq δ : ℝ} (hε : ε ≠ 0)
    (hraw : RawLiftHyp S ε) (hin : InletHyp S ε c) (hinv : InverseBoundHyp S M)
    (hq : QuadraticBoundHyp S Pq) (hF : RawResidualHyp S δ) (hsmall : 4 * Pq * M ^ 2 * δ < 1)
    (hsym : SymmetricClassHyp S (2 * M * δ)) (hcorr : CorrectionHyp S (2 * ε * c) (2 * M * δ))
    (heq : ZeroResidualHyp S (2 * M * δ)) (hdat : DatumHyp S (2 * ε * c) (2 * M * δ))
    (hrem : HeatRemainderHyp S (2 * ε * c) (2 * M * δ)) :
    ∃ (a : SpatialField) (U : ℝ → SpatialField) (Q : ℝ → SobolevGraph.H2),
      IsB3ProjectedOutput ν (2 * ε * c) a U Q := by
  obtain ⟨z, hz, -⟩ := S.exists_isFixed hinv hq hF hsmall hsym
  obtain ⟨Q, hQc, hQp, hQ⟩ := hrem z hz
  exact ⟨_, _, Q, { S.isB3Core_field hε hraw hin hcorr hdat hz hQc hQp hQ with
    projected_equation := heq z hz }⟩

/-- **Theorem B3, literal form, at one parameter point** (`background:thm:B3`, with (2.5) and
the global pressure, unit B0705): as `b3Projected_of_scheme`, with `PressureHyp` in place of
`ZeroResidualHyp`. -/
theorem b3_of_scheme {ε M Pq δ : ℝ} (hε : ε ≠ 0)
    (hraw : RawLiftHyp S ε) (hin : InletHyp S ε c) (hinv : InverseBoundHyp S M)
    (hq : QuadraticBoundHyp S Pq) (hF : RawResidualHyp S δ) (hsmall : 4 * Pq * M ^ 2 * δ < 1)
    (hsym : SymmetricClassHyp S (2 * M * δ)) (hcorr : CorrectionHyp S (2 * ε * c) (2 * M * δ))
    (hpr : PressureHyp S (2 * M * δ)) (hdat : DatumHyp S (2 * ε * c) (2 * M * δ))
    (hrem : HeatRemainderHyp S (2 * ε * c) (2 * M * δ)) :
    ∃ (a : SpatialField) (U : ℝ → SpatialField) (Q : ℝ → SobolevGraph.H2)
      (p : ℝ → Space → ℝ), IsB3Output ν (2 * ε * c) a U Q p := by
  obtain ⟨z, hz, -⟩ := S.exists_isFixed hinv hq hF hsmall hsym
  obtain ⟨Q, hQc, hQp, hQ⟩ := hrem z hz
  obtain ⟨p, hp, hT, hpL2⟩ := hpr z hz
  exact ⟨_, _, Q, p, { S.isB3Core_field hε hraw hin hcorr hdat hz hQc hQp hQ with
    equation := hp
    products_L2 := hT
    pressure_L2 := hpL2 }⟩

end BackgroundScheme

end UnforcedLeray.Cons.C03
