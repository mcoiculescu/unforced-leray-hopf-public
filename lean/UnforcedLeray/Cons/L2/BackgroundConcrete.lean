import UnforcedLeray.Cons.L2.BackgroundConcrete.Operators
import UnforcedLeray.Cons.L2.BackgroundConcrete.Pressure
import UnforcedLeray.Cons.L2.BackgroundConcrete.PressureProjection
import UnforcedLeray.Cons.L2.BackgroundConcrete.HeatL4
import UnforcedLeray.Cons.C03Background

/-!
# Step C3′: the concrete `BackgroundScheme` of Theorem B3

`paper/main.tex`, Section `sec:background` (lines 5060–6018), Theorem B3
(`background:thm:B3`, lines 5093–5141, unit B0705) at the construction's parameters
(lines 13714–13725). Target C03-scheme of the construction half: the free data of
`Cons/C03Background/Scheme.lean` (`BackgroundScheme`) are replaced by the manuscript's objects,
and the hypotheses of `Cons/C03Background.lean` (`SchemeHyps`, `ProjectedEquationHyp`) are
derived from finer named statements about these concrete objects.

## The concrete scheme (`Params.scheme`)

| Field | Concrete object | File |
|---|---|---|
| `train` | B0140's chosen train at `(ν, c)` (lines 2141, 5199; B0140, B0141) | `Fields.lean` |
| `raw` | `U_raw = √s[v₁e_r + (v₂+εH)e_z]`, extended through the axis (line 5200; B0186) | `Fields.lean` |
| `inletProfile`, `inlet` | the cutoff stream lift `E_ε` of the periodized frozen streams `(2Re P_cΔ⁻¹q, −2Im P_cΔ⁻¹q)`, cutoff `χ(s) = smoothTransition(2−4s/H)`, `H = Σ/ν` (lines 5143–5160, 5264–5295; B0303, B0297, B0298) | `Fields.lean` |
| `Y` | `Y_{q₀}`: real, solenoidal, `𝒪`-invariant elements of B0411's `Y_{q₀}` (lines 5085, 5385) | `Spaces.lean` |
| `Z` | `X_{q₀} × ℝ²` with `‖(w,A)‖ = ‖w‖_X + |A|` exactly (`norm_eq_normX_add`; lines 5085–5091, 5698; B0412) | `Spaces.lean` |
| `lin` | the ordinary operator `A₀w + 𝔓B_{U_raw}w + (A₀E_bg + 𝔓B_{U_raw}E_bg)α` (`eq:m3-ordinary-system`; B0684) | `Operators.lean` |
| `inv` | a right inverse of `lin` with the bound (2.31) (B0684) | `Operators.lean` |
| `quad` | `𝔓((e+w)·∇(e'+w'))` with the bound (2.42) (B0458) | `Operators.lean` |
| `rawResidual` | `𝔓F_R` with the bound (2.15) (B0282, B0200) | `Operators.lean` |
| `pair` | `f ↦ (ψ ↦ −∫∫⟨f, ψ⟩)` | `Operators.lean` |
| `sym` | all of `Z` (`Z` carries the symmetry (2.2) and reality, line 5210) | here |
| `corr` | the continuous representative of `w` (`unlabeled:5831`) | `Operators.lean` |
| `coord` | `α = R^{-2/p}A = ε^{8/11}A` (line 5697) | `Operators.lean` |
| `datum` | `a` of (2.8) in the stream form (2.27), stream `ψ(0) + ψ_α` (B0687, B0298) | `Fields.lean` |

The operators are characterised by their pairings with solenoidal phase tests (see
`Operators.lean`); each is a `Classical.choose` of an object with its defining identity (and,
for `inv`, `quad`, `rawResidual`, with the manuscript's bound). Only one object satisfies each
identity, so these are the manuscript's objects; for `inv`, the manuscript's terminal row
`C_H` (2.30) selects one right inverse, and any right inverse with the bound serves (every
fixed point of the closure map is a small solution of the projected equation,
`isSmallSolution_of_isFixed`, and the finer hypotheses below are stated for all small
solutions, which is what the manuscript's arguments for (2.44)–(2.10) use).

## Proved here (no hypothesis)

* `SymmetricClassHyp` (`sym = univ`, `symmetricClassHyp_univ`);
* the lift clauses of `RawLiftHyp` and `InletHyp` (`U_raw` and `E_i` are ring lifts off the
  axis), and the `c`-periodicity of the inlet profiles (`inletProfile_periodic`: the
  periodization `P_c` reindexed by one cell);
* `OrdinarySolveHyp` and `InverseBoundHyp`, `QuadraticBoundHyp`, `RawResidualHyp` from the
  corresponding existence statements (the choices meet their specifications);
* the periodicity clause of `CorrectionClassHyp` (`contRep_periodic`: the representative of an
  element of `Y_{q₀}` is `P`-periodic, by uniqueness of continuous representatives);
* the DSS and symmetry clauses of `DatumHyp` (`datum_dss`, `datum_symmetric`): the datum is
  the ring lift at phase `0` of an age-independent profile, `c`-periodic in `q` because the
  train stream `ψ(0)` (`stream_periodic_of_isTrain`) and the frozen streams are.

## What remains (finer named hypotheses, `ConcreteHyps p B`)

For the concrete objects at `p = (ν, c, ε, Σ, h)` and budget `B = (C, k, m)`
(`P_ν = Cν^{-k}`, `M = P_νe^{m/ν}`, `δ = P_νε^{3/11}`, `ρ = 2Mδ`):

| Hypothesis | Statement | Manuscript | Units |
|---|---|---|---|
| `RawResidualBound` | `𝔓F_R ∈ Y`, `‖𝔓F_R‖ ≤ δ` | (2.15), lines 5197–5205 | B0282, B0200 |
| `OrdinaryOperatorBounded` | the ordinary operator maps `Z` boundedly into `Y` | lines 5152–5154, 5168–5176, (2.21), (2.28) | B0684, B0299 |
| `OrdinaryInverseBound` | it has a right inverse of norm `≤ M` | (2.31)–(2.32) at `β = 0` | B0684, B0682, B0683 |
| `QuadraticBound` | `𝒬` is bounded bilinear `Z × Z → Y`, norm `≤ P_ν` | (2.42), lines 5693–5713 | B0458 |
| `RawLiftRegular` | `U_raw`, `∇U_raw` bounded, smooth, solenoidal | (2.15), `eq:m3-ring-lift` | B0282, B0186, B0189, B0695 |
| `InletRegular` | `E_i`, `∇E_i` bounded, smooth, solenoidal | (2.28) (`‖Eα‖_{W^{j,∞}} ≤ P_j|α|`), (2.27) | B0298, B0299 |
| `CorrectionRegular` | at small solutions, `w` is smooth, bounded with `∇w`, solenoidal, `𝒪`-invariant | (2.3), (2.7), (2.44)–(2.46), `unlabeled:5831` | B0412, B0416, B0688, B0692, B0689–B0691, B0695 |
| `ResidualExpansion` | at small solutions, the weak projected residual of `U` is `⟨𝔓F_R + 𝓛z + 𝒬(z,z), ψ⟩` | (2.44) with (2.15), lines 5714–5727 | B0689, B0282, B0701 |
| `DatumRegular` | at small solutions, `a` is smooth and divergence free off `0`, nonzero, `|D^ka| ≤ C|x|^{-1-k}` | (2.8), lines 5852–5870 | B0687 |
| `HeatRemainder` | at small solutions, `U − H_ν[a] ∈ C_per H²` | (2.10), lines 5909–5993 | B0704, B0703 |

and the train existence `B0140.TrainExistence` (B0141).

**Main results.**
* `Params.schemeHyps_of_concreteHyps`: `SchemeHyps` and `ProjectedEquationHyp` for the concrete
  scheme from `ConcreteHyps`.
* `exists_backgroundScheme`: `BackgroundHyps F B` (what `Cons/C03Background.lean` needs) for a
  record with `ν_n > 0`, `C₀ ≠ 0`, from the train existence and `ConcreteHyps` at the
  concrete parameters `(ν_n, c_n, ε_n, Σ, h)` for all large `n`.
* `stepBackgroundProjected_of_concrete`: C3′ (`StepBackgroundProjected F.withB3`).

Status: the assembly compiles with the standard axioms only; the hypotheses above are OPEN, so
C3′ is not proved. Theorem A is not proved.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped Topology ContDiff ENNReal

namespace UnforcedLeray.Cons.C03.Concrete

open UnforcedLeray.Blueprint UnforcedLeray.Axi UnforcedLeray.Cons.C03 UnforcedLeray.B0140
open UnforcedLeray.Cons.C09

local instance fact_one_le_four_concrete : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩

/-! ## Small solutions of the projected equation -/

/-- `z` is a small solution of the projected equation: `‖z‖ ≤ ρ` and
`𝔓F_R + 𝓛z + 𝒬(z,z) = 0` (lines 5714–5727). -/
def IsSmallSolution {ν c : ℝ} (S : BackgroundScheme ν c) (ρ : ℝ) (z : S.Z) : Prop :=
  ‖z‖ ≤ ρ ∧ S.rawResidual + S.lin z + S.quad z z = 0

/-- A fixed point of the closure map is a small solution, when the inverse solves the ordinary
system. -/
theorem isSmallSolution_of_isFixed {ν c : ℝ} {S : BackgroundScheme ν c} {ρ : ℝ}
    (hsolve : OrdinarySolveHyp S) {z : S.Z} (hz : S.IsFixed ρ z) : IsSmallSolution S ρ z := by
  refine ⟨hz.2.1, ?_⟩
  have h := hsolve (-(S.rawResidual + S.quad z z))
  have hfix : S.inv (-(S.rawResidual + S.quad z z)) = z := hz.2.2
  rw [hfix] at h
  rw [h]
  abel

/-! ## The concrete scheme -/

namespace Params

variable (p : Params)

/-- **The concrete scheme** of Theorem B3 at the parameters `p` and budget `B` (see the module
docstring for each field). -/
def scheme (B : Budget) : BackgroundScheme p.ν p.c where
  train := p.train
  raw := p.raw
  inletProfile := p.inletProfile
  inlet := p.inlet
  Z := p.Z
  Y := p.Y
  inv := p.inv (B.loss p.ν)
  quad := p.quad (B.poly p.ν)
  rawResidual := p.rawRes (B.residual p.ν p.ε)
  lin := p.lin
  pair := p.pair
  sym := univ
  corr := p.corr
  coord := p.coord
  datum := p.datum

/-! ## The finer named hypotheses -/

/-- **`background:eq:2.15`** (lines 5197–5205; units B0282, B0200): the projected raw residual
`𝔓F_R` lies in `Y_{q₀}` with `‖𝔓F_R‖_{Y_{q₀}} ≤ P_νε^{3/11}`. -/
def RawResidualBound (B : Budget) : Prop :=
  ∃ g : p.Y, p.RawRel g ∧ ‖g‖ ≤ B.residual p.ν p.ε

/-- **The ordinary operator is bounded `Z → Y`** (lines 5152–5154: "only its complete equation
source belongs to the body space"; `eq:m3-ordinary-system`, lines 5168–5176; the free graph
bounds (2.21) and the inlet source bound (2.28); units B0684, B0299). -/
def OrdinaryOperatorBounded : Prop :=
  ∃ L : p.Z →L[ℝ] p.Y, ∀ z, p.OrdRel z (L z)

/-- **The ordinary augmented inverse `background:eq:2.31`–`2.32` at terminal value `β = 0`**
(lines 5161–5406, 5670–5691; units B0684, B0682, B0683): the ordinary operator has a bounded
right inverse with `‖w‖_X + R^{2/p}|α| ≤ P_νe^{m/ν}‖f‖_Y`. -/
def OrdinaryInverseBound (B : Budget) : Prop :=
  ∃ T : p.Y →L[ℝ] p.Z, (∀ f, p.lin (T f) = f) ∧ ‖T‖ ≤ B.loss p.ν

/-- **The quadratic estimates `background:eq:2.42`** (lines 5693–5713; unit B0458): the
polarized source `𝔓((e+w)·∇(e'+w'))` is a bounded bilinear map `Z × Z → Y` with norm
`≤ P_ν`. -/
def QuadraticBound (B : Budget) : Prop :=
  ∃ Q : p.Z →L[ℝ] p.Z →L[ℝ] p.Y, (∀ z z', p.QuadRel z z' (Q z z')) ∧ ‖Q‖ ≤ B.poly p.ν

/-- **The raw lift is a smooth bounded solenoidal field** (`background:eq:2.15`:
`‖U_raw‖_{W^{2,∞}} ≤ P`; `eq:m3-ring-lift`: "the complete solenoidal lift"; smooth through the
axis; units B0282, B0186, B0189, B0695). -/
def RawLiftRegular : Prop :=
  IsBoundedBackground p.raw ∧ ∀ τ, IsSolenoidal (p.raw τ)

/-- **The inlet columns are smooth bounded solenoidal fields** (`background:eq:2.28`:
`‖E_εα‖_{W^{j,∞}} ≤ P_j|α|`; (2.27): solenoidal in stream form; units B0298, B0299). -/
def InletRegular : Prop :=
  ∀ i, IsBoundedBackground (p.inlet i) ∧ ∀ τ, IsSolenoidal (p.inlet i τ)

/-- **Regularity of the correction at small solutions** (`background:eq:2.3`, `2.7`,
`2.44`–`2.46`, `unlabeled:5831`; lines 5085–5091, 5115–5122, 5729–5850; units B0412, B0416,
B0688, B0692, B0689, B0690, B0691, B0695): for every small solution `z = (w, A)` of the
projected equation in the ball of radius `2Mδ`, the continuous representative of `w` exists,
is smooth with `w`, `∇w` bounded, and is solenoidal and `𝒪`-invariant at every phase. -/
def CorrectionRegular (B : Budget) : Prop :=
  ∀ z, IsSmallSolution (p.scheme B) (B.radius p.ν p.ε) z →
    IsBoundedBackground (p.corr z) ∧ (∀ τ, IsSolenoidal (p.corr z τ)) ∧
      ∀ τ, IsAxisymmetricNoSwirl (p.corr z τ)

/-- **The residual expansion at small solutions** (`background:eq:2.44` with
`background:eq:2.15`, lines 5197–5205, 5714–5749; units B0689, B0282, B0701): every pairing of
the weak form of `loc:eq:background` converges for `U = U_raw + E_bgα + w`, and its weak
projected residual is the pairing of `𝔓F_R + 𝓛z + 𝒬(z,z)` with the test ("All linear and
quadratic inlet terms are included", line 5726). -/
def ResidualExpansion (B : Budget) : Prop :=
  ∀ z, IsSmallSolution (p.scheme B) (B.radius p.ν p.ε) z →
    HasWeakForm ((p.scheme B).field z) ∧ ∀ ψ, IsSimilarityTest ψ →
      weakResidual p.ν ((p.scheme B).field z) ψ =
        p.pair ((p.scheme B).rawResidual + (p.scheme B).lin z + (p.scheme B).quad z z) ψ

/-- **The datum `background:eq:2.8`** (lines 5123–5129, 5852–5870; unit B0687): at small
solutions, `a = a_{α_bg}` is smooth off `0`, divergence free off `0`, nonzero ("the finite
inlet perturbation [is] exponentially small" on the core, by (2.6)), with
`|D^ka(x)| ≤ C_k|x|^{-1-k}` (`k ≤ 4`). The DSS and symmetry clauses are proved
(`datum_dss`, `datum_symmetric`). -/
def DatumRegular (B : Budget) : Prop :=
  ∀ z, IsSmallSolution (p.scheme B) (B.radius p.ν p.ε) z →
    ContDiffOn ℝ ∞ (p.datum (p.coord z)) {0}ᶜ ∧
      (∀ x : Space, x ≠ 0 → divergence (p.datum (p.coord z)) x = 0) ∧
      (∃ x : Space, x ≠ 0 ∧ p.datum (p.coord z) x ≠ 0) ∧
      ∀ k : ℕ, k ≤ 4 → ∃ C : ℝ, ∀ x : Space, x ≠ 0 →
        ‖iteratedFDeriv ℝ k (p.datum (p.coord z)) x‖ * ‖x‖ ^ (k + 1) ≤ C

/-- **The heat remainder `background:eq:2.10`** (lines 5134–5137, 5909–5993; units B0704,
B0703): at small solutions, `Q := U − H_ν[a] ∈ C_per H²`. -/
def HeatRemainder (B : Budget) : Prop :=
  ∀ z, IsSmallSolution (p.scheme B) (B.radius p.ν p.ε) z →
    ∃ Q : ℝ → SobolevGraph.H2, Continuous Q ∧ Function.Periodic Q p.period ∧
      ∀ τ, ((Q τ).value : SpatialField) =ᵐ[volume]
        (p.scheme B).field z τ - heatProfile p.ν (p.datum (p.coord z)) τ

/-- **The finer named hypotheses of Theorem B3 for the concrete objects** at `p` with budget
`B` (each a manuscript statement; see the module docstring). -/
structure ConcreteHyps (B : Budget) : Prop where
  rawResidual : p.RawResidualBound B
  operator : p.OrdinaryOperatorBounded
  inverse : p.OrdinaryInverseBound B
  quadratic : p.QuadraticBound B
  rawLift : p.RawLiftRegular
  inlet : p.InletRegular
  correction : p.CorrectionRegular B
  expansion : p.ResidualExpansion B
  datum : p.DatumRegular B
  remainder : p.HeatRemainder B

/-! ## The hypotheses of the scheme -/

variable {p}

theorem ordinarySolveHyp {B : Budget} (h : p.OrdinaryInverseBound B) :
    OrdinarySolveHyp (p.scheme B) :=
  (p.inv_spec h).1

theorem inverseBoundHyp {B : Budget} (h : p.OrdinaryInverseBound B) :
    InverseBoundHyp (p.scheme B) (B.loss p.ν) :=
  (p.inv_spec h).2

theorem quadraticBoundHyp {B : Budget} (h : p.QuadraticBound B) :
    QuadraticBoundHyp (p.scheme B) (B.poly p.ν) :=
  (p.quad_spec h).2

theorem rawResidualHyp {B : Budget} (h : p.RawResidualBound B) :
    RawResidualHyp (p.scheme B) (B.residual p.ν p.ε) :=
  (p.rawRes_spec h).2

theorem symmetricClassHyp (B : Budget) (ρ : ℝ) : SymmetricClassHyp (p.scheme B) ρ :=
  symmetricClassHyp_univ (p.scheme B) rfl ρ

theorem rawLiftHyp {B : Budget} (h : p.RawLiftRegular) : RawLiftHyp (p.scheme B) p.ε where
  lift τ y hy := p.raw_eq_off_axis τ y hy
  bounded := h.1
  solenoidal := h.2

theorem inletHyp {B : Budget} (h : p.InletRegular) : InletHyp (p.scheme B) p.ε p.c where
  profile_periodic i s _ ξ η := p.inletProfile_periodic i s ξ η
  lift _ _ _ _ := rfl
  bounded i := (h i).1
  solenoidal i := (h i).2

theorem correctionClassHyp {B : Budget} (hinv : p.OrdinaryInverseBound B)
    (h : p.CorrectionRegular B) :
    CorrectionClassHyp (p.scheme B) (2 * p.ε * p.c) (B.radius p.ν p.ε) := fun z hz =>
  have hs := h z (isSmallSolution_of_isFixed (ordinarySolveHyp hinv) hz)
  ⟨p.corr_periodic z, hs.2.1, hs.2.2⟩

theorem correctionBoundsHyp {B : Budget} (hinv : p.OrdinaryInverseBound B)
    (h : p.CorrectionRegular B) : CorrectionBoundsHyp (p.scheme B) (B.radius p.ν p.ε) :=
  fun z hz => (h z (isSmallSolution_of_isFixed (ordinarySolveHyp hinv) hz)).1

theorem residualExpansionHyp {B : Budget} (hinv : p.OrdinaryInverseBound B)
    (h : p.ResidualExpansion B) : ResidualExpansionHyp (p.scheme B) (B.radius p.ν p.ε) :=
  fun z hz => h z (isSmallSolution_of_isFixed (ordinarySolveHyp hinv) hz)

/-- At the selected fixed point, the residual expansion supplies the tensor-column L² bounds.
Applying the concrete Riesz construction to those actual columns gives an actual phasewise L²
pressure; this package contains no assumed pressure field. -/
theorem canonicalPressureData_of_fixed {B : Budget} (H : p.ConcreteHyps B)
    {z : (p.scheme B).Z} (hz : (p.scheme B).IsFixed (B.radius p.ν p.ε) z) :
    ∃ p₀ : ℝ → Space → ℝ,
      (∀ τ, ColumnsL2 (tensorColumns ((p.scheme B).field z τ) ((p.scheme B).field z τ))) ∧
      (∀ τ, MemLp (p₀ τ) 2 volume) ∧
      (∀ τ Φ, IsSpatialTest Φ →
        colPairing
          (stressL2 ((p.scheme B).field z) p₀ τ) (hessL2 Φ) = 0) := by
  let hsmall := isSmallSolution_of_isFixed (ordinarySolveHyp H.inverse) hz
  let hw := (H.expansion z hsmall).1
  let hU : ∀ τ, ColumnsL2
      (tensorColumns ((p.scheme B).field z τ) ((p.scheme B).field z τ)) :=
    fun τ => hw.tensor_memL2 τ
  refine ⟨stressPressure ((p.scheme B).field z) hU, hU, ?_, ?_⟩
  · intro τ
    exact stressPressure_memLp ((p.scheme B).field z) hU τ
  · intro τ Φ hΦ
    exact stressPressure_c09Relation_path ((p.scheme B).field z) hU τ hΦ

/-- The L²-valued canonical pressure path at the selected fixed point inherits the actual
background period. This uses periodicity of the concrete raw, inlet, and correction pieces; it
does not assume a pressure path. -/
theorem canonicalPressurePath_periodic_of_fixed {B : Budget} (H : p.ConcreteHyps B)
    {z : (p.scheme B).Z} (hz : (p.scheme B).IsFixed (B.radius p.ν p.ε) z) :
    Function.Periodic
      (stressPressureL2Path ((p.scheme B).field z)
        (fun τ => (H.expansion z
          (isSmallSolution_of_isFixed (ordinarySolveHyp H.inverse) hz)).1.tensor_memL2 τ))
      (2 * p.ε * p.c) := by
  let hsmall := isSmallSolution_of_isFixed (ordinarySolveHyp H.inverse) hz
  let hU : ∀ τ, ColumnsL2
      (tensorColumns ((p.scheme B).field z τ) ((p.scheme B).field z τ)) :=
    fun τ => (H.expansion z hsmall).1.tensor_memL2 τ
  have hpiece : IsBackgroundPiece (2 * p.ε * p.c) ((p.scheme B).field z) :=
    (p.scheme B).isBackgroundPiece_field p.ε_pos.ne'
      (p.rawLiftHyp H.rawLift) (p.inletHyp H.inlet)
      (correctionHyp_of (p.scheme B)
        (p.correctionClassHyp H.inverse H.correction)
        (p.correctionBoundsHyp H.inverse H.correction)) hz
  exact periodic_stressPressureL2Path ((p.scheme B).field z) hU
    (fun i j => periodic_tensorEntryL2 ((p.scheme B).field z) hU hpiece.periodic i j)

/-- The actual fixed-point datum and its recorded weighted derivative bounds give an L⁴
continuous path for the heat profile subtracted in `HeatRemainder`. -/
theorem heatProfileL4_of_fixed {B : Budget} (H : p.ConcreteHyps B)
    {z : (p.scheme B).Z} (hz : (p.scheme B).IsFixed (B.radius p.ν p.ε) z) :
    ∃ W : ℝ → Lp Space 4 volume, Continuous W ∧
      ∀ τ, (W τ : Space → Space) =ᵐ[volume]
        heatProfile p.ν (p.datum (p.coord z)) τ := by
  let hsmall := isSmallSolution_of_isFixed (ordinarySolveHyp H.inverse) hz
  obtain ⟨W, hWc, hW⟩ := exists_continuous_heatProfile_L4_of_datum p.ν_pos
    (H.datum z hsmall).1 (H.datum z hsmall).2.2.2
  exact ⟨W, hWc, hW⟩

/-- The concrete fixed-point field has a continuous L⁴ representative in phase: add the heat
profile path to the H² remainder path, and use the recorded a.e. remainder identity. -/
theorem field_continuous_L4_of_fixed {B : Budget} (H : p.ConcreteHyps B)
    {z : (p.scheme B).Z} (hz : (p.scheme B).IsFixed (B.radius p.ν p.ε) z) :
    ∃ W : ℝ → Lp Space 4 volume, Continuous W ∧
      ∀ τ, (W τ : SpatialField) =ᵐ[volume] (p.scheme B).field z τ := by
  let hsmall := isSmallSolution_of_isFixed (ordinarySolveHyp H.inverse) hz
  obtain ⟨Q, hQc, _hQp, hQ⟩ := H.remainder z hsmall
  obtain ⟨Hpath, hHc, hH⟩ := heatProfileL4_of_fixed H hz
  let W : ℝ → Lp Space 4 volume := fun τ => Hpath τ + h2ValueL4 (Q τ)
  refine ⟨W, ?_, ?_⟩
  · exact hHc.add (continuous_h2Value_L4 Q hQc)
  · intro τ
    filter_upwards [Lp.coeFn_add (Hpath τ) (h2ValueL4 (Q τ)), hH τ,
      h2Value_L4_ae (Q τ), hQ τ] with y hsum hheat hrem hremEq
    calc
      (W τ : SpatialField) y = (Hpath τ : SpatialField) y +
          (h2ValueL4 (Q τ) : SpatialField) y := hsum
      _ = (p.scheme B).field z τ y := by
        rw [hheat, hrem, hremEq]
        rw [add_comm]
        exact sub_add_cancel _ _

/-- The actual fixed-point canonical Riesz pressure is continuous as an L²-valued path.
The continuity is derived from the continuous L⁴ representative of the field and the bounded
bilinear stress map. -/
theorem canonicalPressurePath_continuous_of_fixed {B : Budget} (H : p.ConcreteHyps B)
    {z : (p.scheme B).Z} (hz : (p.scheme B).IsFixed (B.radius p.ν p.ε) z) :
    Continuous
      (stressPressureL2Path ((p.scheme B).field z)
        (fun τ => (H.expansion z
          (isSmallSolution_of_isFixed (ordinarySolveHyp H.inverse) hz)).1.tensor_memL2 τ)) := by
  let hsmall := isSmallSolution_of_isFixed (ordinarySolveHyp H.inverse) hz
  let hU : ∀ τ, ColumnsL2
      (tensorColumns ((p.scheme B).field z τ) ((p.scheme B).field z τ)) :=
    fun τ => (H.expansion z hsmall).1.tensor_memL2 τ
  obtain ⟨W, hWc, hW⟩ := field_continuous_L4_of_fixed H hz
  exact continuous_stressPressureL2Path ((p.scheme B).field z) hU
    (fun i j => continuous_tensorEntryL2_of_L4 ((p.scheme B).field z) hU W hWc hW i j)

#print axioms canonicalPressurePath_continuous_of_fixed

theorem datumHyp {B : Budget} (hinv : p.OrdinaryInverseBound B) (h : p.DatumRegular B) :
    DatumHyp (p.scheme B) (2 * p.ε * p.c) (B.radius p.ν p.ε) := fun z hz =>
  have hs := h z (isSmallSolution_of_isFixed (ordinarySolveHyp hinv) hz)
  { smooth := hs.1
    div_free := hs.2.1
    nonzero := hs.2.2.1
    dss := fun x _ => p.datum_dss (p.coord z) x
    bounds := hs.2.2.2
    symmetric := p.datum_symmetric (p.coord z) }

theorem heatRemainderHyp {B : Budget} (hinv : p.OrdinaryInverseBound B)
    (h : p.HeatRemainder B) :
    HeatRemainderHyp (p.scheme B) (2 * p.ε * p.c) (B.radius p.ν p.ε) :=
  fun z hz => h z (isSmallSolution_of_isFixed (ordinarySolveHyp hinv) hz)

/-- **The hypotheses of Theorem B3 for the concrete scheme** (`SchemeHyps` and
`ProjectedEquationHyp` of `Cons/C03Background.lean`) from the finer named hypotheses. -/
theorem schemeHyps_of_concreteHyps {B : Budget} (H : p.ConcreteHyps B) :
    SchemeHyps (p.scheme B) B p.ε ∧ ProjectedEquationHyp (p.scheme B) B p.ε :=
  ⟨{ rawLift := rawLiftHyp H.rawLift
     inlet := inletHyp H.inlet
     inverse := inverseBoundHyp H.inverse
     quadratic := quadraticBoundHyp H.quadratic
     rawResidual := rawResidualHyp H.rawResidual
     symClass := symmetricClassHyp B _
     correctionClass := correctionClassHyp H.inverse H.correction
     correctionBounds := correctionBoundsHyp H.inverse H.correction
     datum := datumHyp H.inverse H.datum
     remainder := heatRemainderHyp H.inverse H.remainder },
   { solve := ordinarySolveHyp H.inverse
     expansion := residualExpansionHyp H.inverse H.expansion }⟩

/-- **Theorem B3 (projected form) at the concrete parameters**, from the finer hypotheses and the
smallness `4PM²δ < 1` of (2.43). -/
theorem b3ProjectedAt_of_concreteHyps {B : Budget} (H : p.ConcreteHyps B)
    (hsmall : B.smallness p.ν p.ε < 1) : B3ProjectedAt p.ν (2 * p.ε * p.c) := by
  obtain ⟨hS, hE⟩ := schemeHyps_of_concreteHyps H
  exact b3ProjectedAt_of_hyps p.ε_pos.ne' hS
    (zeroResidualHyp_of_expansion _ hE.solve hE.expansion) hsmall

end Params

/-! ## Along the construction's sequence -/

/-- `c_n = ν_n^{-2} > 0`. -/
theorem spacing_pos {F : ConstructionData} {n : ℕ} (hν : 0 < F.ν n) : 0 < F.spacing n := by
  unfold ConstructionData.spacing
  positivity

/-- **The parameters at level `n`** (lines 13714–13725): `ν = ν_n`, `c = c_n = ν_n^{-2}`,
`ε = ε_n`, the fixed slow age `Σ`, and the planar eigenvorticity profile of the record. -/
def levelParamsOfTrain (F : ConstructionData) (hν : ∀ n, 0 < F.ν n) (hC : F.C₀ ≠ 0)
    {Sig : ℝ} (hSig : 0 < Sig) (n : ℕ)
    (tr : TrainSol (F.ν n) (F.spacing n)) : Params where
  ν := F.ν n
  c := F.spacing n
  ε := F.amplitude n
  ageCut := Sig
  mode := F.planar.mode
  ν_pos := hν n
  c_pos := spacing_pos (hν n)
  ε_pos := amplitude_pos_of hC (hν n)
  ageCut_pos := hSig
  trainData := tr

/-- Compatibility constructor for callers that only know the source existence proposition. Its
chosen train is stored once in the resulting `Params`; all raw and scheme objects use that value. -/
def levelParams (F : ConstructionData) (hν : ∀ n, 0 < F.ν n) (hC : F.C₀ ≠ 0) {Sig : ℝ}
    (hSig : 0 < Sig) (n : ℕ) (hT : TrainIVPSolvable (F.ν n) (F.spacing n)) : Params :=
  levelParamsOfTrain F hν hC hSig n (B0140.train hT)

/-- **The finer hypotheses along the sequence**: for all large `n`, `ConcreteHyps` holds for the
concrete objects at `(ν_n, c_n, ε_n, Σ, h)` with one budget `B`. -/
def ConcreteBackgroundHyps (F : ConstructionData) (hν : ∀ n, 0 < F.ν n) (hC : F.C₀ ≠ 0)
    {Sig : ℝ} (hSig : 0 < Sig) (B : Budget) : Prop :=
  ∀ᶠ n in atTop, ∀ hT : TrainIVPSolvable (F.ν n) (F.spacing n),
    (levelParams F hν hC hSig n hT).ConcreteHyps B

/-- The eventual concrete background construction with one explicit actual train witness at each
level. This is the construction-facing interface: strong train estimates proved for `tr` feed the
same `Params.trainData`, `Params.raw`, `Params.datum`, and `scheme.train`. -/
def ConcreteBackgroundHypsOfTrain (F : ConstructionData) (hν : ∀ n, 0 < F.ν n)
    (hC : F.C₀ ≠ 0) {Sig : ℝ} (hSig : 0 < Sig) (B : Budget) : Prop :=
  ∀ᶠ n in atTop, ∃ tr : TrainSol (F.ν n) (F.spacing n),
    (levelParamsOfTrain F hν hC hSig n tr).ConcreteHyps B

/-- The train exists at `(ν_n, c_n)` for all large `n`, from B0140's `TrainExistence`
(`Train.per ν = ν⁻²`, B0141). -/
theorem eventually_trainIVPSolvable {F : ConstructionData} (hν : ∀ n, 0 < F.ν n)
    (hν0 : Tendsto F.ν atTop (𝓝 0)) (hT : TrainExistence) :
    ∀ᶠ n in atTop, TrainIVPSolvable (F.ν n) (F.spacing n) := by
  obtain ⟨ν₀, hν₀, h⟩ := hT
  filter_upwards [hν0.eventually (Iio_mem_nhds hν₀)] with n hn
  have := h (F.ν n) ⟨hν n, le_of_lt hn⟩
  rwa [Train.per, inv_pow] at this

/-- **`exists_backgroundScheme`: the background hypotheses of `Cons/C03Background.lean`**
(`BackgroundHyps F B`: for all large `n` a scheme at `(ν_n, c_n)` meeting `SchemeHyps` and
`ProjectedEquationHyp` at `ε_n`), with the concrete scheme `Params.scheme`, from the train
existence (B0141) and the finer named hypotheses about the concrete objects. -/
theorem exists_backgroundScheme {F : ConstructionData} (hν : ∀ n, 0 < F.ν n)
    (hν0 : Tendsto F.ν atTop (𝓝 0)) (hC : F.C₀ ≠ 0) {Sig : ℝ} (hSig : 0 < Sig) {B : Budget}
    (hT : TrainExistence) (H : ConcreteBackgroundHyps F hν hC hSig B) :
    BackgroundHyps F B := by
  filter_upwards [H, eventually_trainIVPSolvable hν hν0 hT] with n hn hTn
  exact ⟨(levelParams F hν hC hSig n hTn).scheme B,
    Params.schemeHyps_of_concreteHyps (hn hTn)⟩

/-- The concrete scheme can be assembled directly from the same explicit train witness that its
raw lift and datum use. -/
theorem exists_backgroundScheme_of_witnessedTrain {F : ConstructionData}
    (hν : ∀ n, 0 < F.ν n) (hC : F.C₀ ≠ 0) {Sig : ℝ} (hSig : 0 < Sig) {B : Budget}
    (H : ConcreteBackgroundHypsOfTrain F hν hC hSig B) : BackgroundHyps F B := by
  filter_upwards [H] with n hn
  obtain ⟨tr, hConcrete⟩ := hn
  exact ⟨(levelParamsOfTrain F hν hC hSig n tr).scheme B,
    Params.schemeHyps_of_concreteHyps hConcrete⟩

/-- **Step C3′** (`StepBackgroundProjected`, lines 5093–5141, 13714–13725, unit B0705) for
`F.withB3`, from the train existence, the finer named hypotheses about the concrete objects and
a budget with `22m < γ`. -/
theorem stepBackgroundProjected_of_concrete {F : ConstructionData} (hν : ∀ n, 0 < F.ν n)
    (hν0 : Tendsto F.ν atTop (𝓝 0)) (hC : F.C₀ ≠ 0) {Sig : ℝ} (hSig : 0 < Sig) {B : Budget}
    (hm : 22 * B.m < F.growth) (hT : TrainExistence)
    (H : ConcreteBackgroundHyps F hν hC hSig B) : StepBackgroundProjected F.withB3 :=
  stepBackgroundProjected_of_hyps hν hν0 hC hm (exists_backgroundScheme hν hν0 hC hSig hT H)

/-- The projected background step for explicitly witnessed train data. -/
theorem stepBackgroundProjected_of_witnessedTrain {F : ConstructionData}
    (hν : ∀ n, 0 < F.ν n) (hν0 : Tendsto F.ν atTop (𝓝 0)) (hC : F.C₀ ≠ 0)
    {Sig : ℝ} (hSig : 0 < Sig) {B : Budget} (hm : 22 * B.m < F.growth)
    (H : ConcreteBackgroundHypsOfTrain F hν hC hSig B) : StepBackgroundProjected F.withB3 :=
  stepBackgroundProjected_of_hyps hν hν0 hC hm
    (exists_backgroundScheme_of_witnessedTrain hν hC hSig H)

end UnforcedLeray.Cons.C03.Concrete

#print axioms UnforcedLeray.Cons.C03.Concrete.Params.schemeHyps_of_concreteHyps
#print axioms UnforcedLeray.Cons.C03.Concrete.exists_backgroundScheme
#print axioms UnforcedLeray.Cons.C03.Concrete.exists_backgroundScheme_of_witnessedTrain
#print axioms UnforcedLeray.Cons.C03.Concrete.stepBackgroundProjected_of_concrete
#print axioms UnforcedLeray.Cons.C03.Concrete.stepBackgroundProjected_of_witnessedTrain
#print axioms UnforcedLeray.Cons.C03.Concrete.Params.datum_dss
#print axioms UnforcedLeray.Cons.C03.Concrete.contRep_periodic
