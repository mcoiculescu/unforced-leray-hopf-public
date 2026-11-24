import UnforcedLeray.Short.PartIIIb.NearInst

/-!
# Targets for the concrete near operators (source 3405-3581, 3861-4132)

Source of record: `the November 2 reference manuscript`.  All statements are over the
concrete objects of `NearInst.lean`: the background level `p : Params` in the regime
`IIb.BgRegime p d d₋ d₊` (`c = ν⁻²`, `ε = e^{-d/ν}`), the actual train `p.trainData`, the exact split
`IIb.ExactSplitII p ρ_b S_in V r_b` with `ρ_b = IIb.rhoB p m₀ C₀ k₀`, the gain exponent
`γ = Re λ` of a planar reference `P`, and operators satisfying the pins `IsActualNear`.

`P_ν` (a fixed viscosity polynomial) is written `C ν⁻ᵏ`.

## Flat-causal module (3405-3581)

* `FreeStressExists` : `S₀` exists as a bounded operator `Z → H` (3427-3440, free case, with the
  free energy bound; ungained norms are bounded because `1 ≤ g ≤ e^{γ/ν}`).
* `CoeffMultExists` : a coefficient `w` with `√s W|w| ≤ B` defines the bounded multiplier
  `u ↦ w⊗u + u⊗w` (2764-2775).
* `FlatTrainMultBound` : the actual train multiplier bound `sup √s W|v_flat| ≤ P_ν` for the BUC
  train of `sct:train` (`PartI.IsBUCTrain`, 270-288, 2040), the hypothesis of
  `cor:short-polynomial-stress` (2714-2729, 3566-3567).
* `NearFlatBoundC` : `near:flat-bound` (3881-3887) from `cor:short-polynomial-stress`
  (3560-3581): `D₀` is invertible and `‖G⁻¹D₀⁻¹G‖_{Z→Z} ≤ P_ν`.

## Equation comparison and bin decomposition (3861-4132)

* `SplitMultBound` : `sup √s W|v| ≤ P_ν` and `√s|v_b| ≤ ρ_b` for the exact split (2716, 2775-2777).
* `MaskedNearExists` : `S_ε` (real form of `PartIIa.Teps`-stress map) and `S_far` (kernel realization,
  positive majorant `C|x|^{-4}` of `sep:kernel`, 3996-4011) exist as bounded operators.
* `NearDeltaBoundC` : `near:deltaN` (3927-3942, proof 3956-4053).
* `NearMaskedFreeBoundC` : `near:masked-free-bound` (4023-4031).
* `NearSolverC` : `near:inverse-comparison` (3943-3951) under the parameter choice (4109-4124), with
  `near:masked-free-bound`: the near clauses of `PairNormAndNearSolver` (5540-5547).
* `BodyRealForms` : the body inverses `T_ε`, `T_0` (1675-1677) have real forms on `H`.
* `ForcedColumnC` : the forced-column comparison (4079-4132), the near input of
  `CurvedFlatComparison` (5896-5899).
* `NearOpsExistC` : the pinned operators exist at every level of the regime (assembly).

## The slow data of the inlet (`ORG:stmt/PartIII-a/ParamsWideQuantifiers`)

The exact split `V = U_raw + E_εα` contains the inlet `p.inlet i`, linear in the free field
`p.mode` and cut at the age `H = Σ/ν`, `Σ = p.ageCut` (`IIb.BgRegime` constrains neither). In the
source it is the fixed Gaussian angular-two eigenstream of the frozen growing pair (2048-2049,
2347-2358, 2385-2387), whose bounds enter the constants. So every statement below over
`IIb.ExactSplitII` fixes a slow age `Σ > 0` before the constants and restricts to the levels with
`p.ageCut = Σ` and `p.mode = q`, where the eigenpair is that of the planar reference
(`p.mode = P.mode`, `IsPlanarReference.eigenpair`) when the statement has one, and otherwise a
fixed `IsGrowingEigenpair λ q` (as in `IIIa.StressCoefficients`, `IIb.ExactSplitExport`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst

open UnforcedLeray.Short.PartIIIb.Concrete UnforcedLeray.Cons.C03.Concrete
  UnforcedLeray.Blueprint.Planar

/-- `η_δ = γ tanh(3δ/8)` (source 4002-4007). -/
def etaDelta (γ δ : ℝ) : ℝ := γ * Real.tanh (3 * δ / 8)

/-- `θ = min{a/2, b/2, 1/100, 3/22}` (source 4113). -/
def thetaAB (a b : ℝ) : ℝ := min (min (a / 2) (b / 2)) (min (1 / 100) (3 / 22))

/-! ## Flat-causal module (3405-3581) -/

/-- **The flat free response is a bounded operator** (source 3427-3440 with `v = 0`, 1686-1689):
for `K ⋐ (0, 1/4)` and small `ν`, `c = ν⁻²`, every `m_Z ≥ 0`, `ρ_b > 0`, there is
`S : Z → H` with `IsFreeStress S ν μ`.  (Existence and uniqueness of the causal zero-entrance energy
solution: `IIIa.FreeCausalExistsUnique`; linearity: `IIIa.CausalSolSub`; boundedness: the energy
bound and `‖F₁ + F₂‖_𝒯 ≤ ‖F‖_Z` for `W ≥ 1`.) -/
def FreeStressExists : Prop :=
  ∀ P : PlanarData, IsPlanarReference P → ∀ Kset : Set ℝ, IsCompact Kset →
    Kset ⊆ Ioo 0 (1 / 4) → ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν ∈ Ioc 0 ν₀, ∀ c : ℝ, c = (ν ^ 2)⁻¹ →
      ∀ μ ∈ Kset, ∀ mZ ρb : ℝ, 0 ≤ mZ → 0 < ρb →
        ∃ S : Zsp c mZ ρb →L[ℝ] Hsp c, IsFreeStress S ν μ

/-- **Coefficient multipliers** (source 2764-2775: "the ratio of stress and velocity age densities is
`s`", `|a⊗b + b⊗a| ≤ 2|a||b|`): measurable coefficients `w₁, w₂` with `√s W|w₁| ≤ B₁` and
`√s|w₂| ≤ B₂` define a bounded `M : H → Z` with `M u = (w₁⊗u + u⊗w₁, w₂⊗u + u⊗w₂)`. -/
def CoeffMultExists : Prop :=
  ∀ (c mZ ρb B₁ B₂ : ℝ) (w₁ w₂ : Chart → Merid), 0 < c → 0 < ρb →
    Measurable w₁ → Measurable w₂ →
    (∀ p : Chart, 0 < p.1 →
      Real.sqrt p.1 * UnforcedLeray.Short.IIIa.transWeight mZ p * ‖w₁ p‖ ≤ B₁) →
    (∀ᵐ p ∂(ageμ c (-1 / 2)), Real.sqrt p.1 * ‖w₂ p‖ ≤ B₂) →
    ∃ M : Hsp c →L[ℝ] Zsp c mZ ρb, ∀ u : Hsp c,
      ((M u).fst : Chart → Ten3) =ᵐ[z1Measure c mZ]
          (fun p => ten3Of (UnforcedLeray.Short.IIIa.symOuter (w₁ p) (u p))) ∧
        ((M u).snd : Chart → Ten3) =ᵐ[htRhoMeasure c ρb]
          (fun p => ten3Of (UnforcedLeray.Short.IIIa.symOuter (w₂ p) (u p)))

/-- **The actual train multiplier bound** (source 2714-2729 for the flat train, 3566-3567): for
`m_Z > 3/2` there are `C, k, ν₀` with `√s W |v_flat(s, q, η)| ≤ C ν^{-k}` for every BUC train at
`(ν, ν⁻²)`, `ν ≤ ν₀`, and every `s > 0`; `v_flat` is measurable.

The class of the train: the train of the source is the Gallay-Slijepcevic solution in `BUC` of
Proposition `sct:train` (source 270-288: "a unique global mild solution in `BUC`"; 2040: "Let `v_c`
be the train of Proposition `sct:train`"), and the bound comes from `sct:fluctuation`, `sct:mean`
and `sct:expansion` (397-459), which Part I states for `PartI.IsBUCTrain`
(`Short/PartI/TrainClass.lean`); `B0140.IsTrain` alone has no time-uniform bound and does not
determine the train.  Hence the hypothesis `PartI.IsBUCTrain tr`, supplied at the actual train
`p.trainData` by the field `train_buc` of `IIb.BgRegime`.  This is `FlatTrainMultBoundBUC`
(`NearInst/FlatTrain/Defs.lean`) by `Iff.rfl` (`NearInst/FlatTrain/Bridge.lean`). -/
def FlatTrainMultBound : Prop :=
  ∀ mZ : ℝ, 3 / 2 < mZ → ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < ν₀ ∧ ∀ ν ∈ Ioc 0 ν₀,
    ∀ c : ℝ, c = (ν ^ 2)⁻¹ → ∀ tr : UnforcedLeray.B0140.TrainSol ν c,
      UnforcedLeray.Short.PartI.IsBUCTrain tr → Measurable (trainMer tr) ∧
      ∀ p : Chart, 0 < p.1 →
        Real.sqrt p.1 * UnforcedLeray.Short.IIIa.transWeight mZ p * ‖trainMer tr p‖ ≤ C * ν⁻¹ ^ k

/-- **`near:flat-bound`** (source 3881-3887), from `cor:short-polynomial-stress` (3560-3581,
`D₀⁻¹ = I - M₀S_lin`): for a planar reference (gain `γ = Re λ`), `K ⋐ (0, 1/4)`, `m_Z > 3/2`, there
are `C, k, ν₀` such that at every level `p` of the regime with `ν ≤ ν₀`, every `0 < ρ_b ≤ 1`,
`μ ∈ K` and operators with the flat pins, `D₀` is a unit and `‖G⁻¹D₀⁻¹G‖_{Z→Z} ≤ C ν^{-k}`. -/
def NearFlatBoundC : Prop :=
  ∀ P : PlanarData, IsPlanarReference P → ∀ Kset : Set ℝ, IsCompact Kset →
    Kset ⊆ Ioo 0 (1 / 4) → ∀ mZ : ℝ, 3 / 2 < mZ → ∀ dm dp : ℝ, 0 < dm →
    ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < ν₀ ∧
      ∀ (p : Params) (d : ℝ), UnforcedLeray.Short.IIb.BgRegime p d dm dp → p.ν ≤ ν₀ →
      ∀ ρb : ℝ, 0 < ρb → ρb ≤ 1 → ∀ μ ∈ Kset, ∀ o : NearOps p.c mZ ρb,
        IsFlatMult o.M0 p.trainData → IsFreeStress o.S0 p.ν μ →
        IsUnit o.D0 ∧
          ‖conjG (gainEquiv p.c mZ ρb P.eigenvalue.re p.ν_pos) (Ring.inverse o.D0)‖ ≤
            C * p.ν⁻¹ ^ k

/-! ## Equation comparison and bin decomposition (3861-4132) -/

/-- **The exact split coefficients** (source 2716 first line, 2775-2777; `√s v_b = r_b`): for
`m_Z > 3/2`, `0 < m₀ ≤ 3d₋/11` and `C₀, k₀`, there are `C, k, ν₀` such that at every level of the
regime with `ν ≤ ν₀` and every exact split, `v = chartCoeff R V` and `v_b = chartCoeff R r_b` are
measurable, `√s W|v| ≤ C ν^{-k}` for `s > 0`, and `√s|v_b| ≤ ρ_b` a.e.  The slow age `Σ > 0` and
the growing eigenpair `(λ, q)` of the inlet are fixed before the constants, at the levels with
`p.ageCut = Σ`, `p.mode = q` (2048-2049, 2347-2358; as in `IIIa.StressCoefficients`). -/
def SplitMultBound : Prop :=
  ∀ dm dp : ℝ, 0 < dm → ∀ (m0 C0 : ℝ) (k0 : ℕ), 0 < m0 → m0 ≤ 3 * dm / 11 → 0 < C0 →
    ∀ mZ : ℝ, 3 / 2 < mZ →
    ∀ (Sig : ℝ) (lam : ℂ) (q : UnforcedLeray.Blueprint.Planar.Profile), 0 < Sig →
      UnforcedLeray.Blueprint.Planar.IsGrowingEigenpair lam q →
    ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < ν₀ ∧
      ∀ (p : Params) (d : ℝ), UnforcedLeray.Short.IIb.BgRegime p d dm dp → p.ν ≤ ν₀ →
      p.ageCut = Sig → p.mode = q →
      ∀ (S_in : ℝ) (V rb : ℝ → UnforcedLeray.SpatialField),
        UnforcedLeray.Short.IIb.ExactSplitII p (UnforcedLeray.Short.IIb.rhoB p m0 C0 k0) S_in V rb →
        Measurable (UnforcedLeray.Short.IIIa.chartCoeff p.R V) ∧
          Measurable (UnforcedLeray.Short.IIIa.chartCoeff p.R rb) ∧
          (∀ pt : Chart, 0 < pt.1 → Real.sqrt pt.1 * UnforcedLeray.Short.IIIa.transWeight mZ pt *
            ‖UnforcedLeray.Short.IIIa.chartCoeff p.R V pt‖ ≤ C * p.ν⁻¹ ^ k) ∧
          (∀ᵐ pt ∂(ageμ p.c (-1 / 2)), Real.sqrt pt.1 *
            ‖UnforcedLeray.Short.IIIa.chartCoeff p.R rb pt‖ ≤ UnforcedLeray.Short.IIb.rhoB p m0 C0 k0)

/-- **The masked curved free inverse exists** (source 1675-1690 `near:free-energy` for `S_ε`, and the
positive-majorant estimate 3996-4011 for the separated part `S_far`): for `K ⋐ (0,1/4)`,
`m_Z ≥ 0`, `0 < b < 1`, `δ > 0`, there is a threshold `ν₀` such that for every `ρ_b > 0`, at every
level of the regime with `ν ≤ ν₀` and `μ ∈ K`, there is `S_N : Z → H` with
`IsMaskedNear p μ δ ε^{-b} S_N`.  The operators `S_ε`, `S_far` do not depend on `ρ_b` (it only fixes
the carrier `Z = Z₁ ⊕ ρ_b^{-1/2} H_T`), and the threshold only makes `P = 2εc ≤ 1`. -/
def MaskedNearExists : Prop :=
  ∀ Kset : Set ℝ, IsCompact Kset → Kset ⊆ Ioo 0 (1 / 4) → ∀ mZ : ℝ, 0 ≤ mZ →
    ∀ b δ : ℝ, 0 < b → b < 1 → 0 < δ → ∀ dm dp : ℝ, 0 < dm → ∃ ν₀ : ℝ, 0 < ν₀ ∧
      ∀ (p : Params) (d : ℝ), UnforcedLeray.Short.IIb.BgRegime p d dm dp → p.ν ≤ ν₀ →
      ∀ ρb : ℝ, 0 < ρb →
      ∀ μ ∈ Kset, ∃ SN : Zsp p.c mZ ρb →L[ℝ] Hsp p.c, IsMaskedNear p μ δ (p.ε ^ (-b)) SN

/-- **`near:deltaN`** (source 3927-3942; proof 3956-4053): for a planar reference (`γ = Re λ`),
`K ⋐ (0, 1/4)`, `m_Z > 3/2` and the window `[d₋, d₊]`, there is a fixed integer `K`, chosen before
`a, b`, such that for `a, b, δ, m₀, D_⊥` (`0 < b < 1`, `0 < m₀ < 3d₋/11`) and `C₀, k₀` there are
`C, k, ν₀` with: at every level of the regime with `ν ≤ ν₀`, every exact split with
`ρ_b = rhoB p m₀ C₀ k₀` and inlet support `S_in ≤ S = ε^{-b}`, `μ ∈ K`, and the actual near operators,
`δ_N = ‖G⁻¹(D_N - D₀)G‖ ≤ C ν^{-k} [ε^{a/2} + ε^{b/2} + ε e^{(m₀+η_δ)/ν}
  + ε^{1/50-K(a+b)} e^{η_δ/ν} + ε^{3/22} e^{(η_δ+m₀/2)/ν} + e^{-(D_⊥-η_δ)/ν}]`,
`η_δ = γ tanh(3δ/8)`.  The slow age `Σ > 0` of the inlet is fixed before the constants, at the
levels with `p.ageCut = Σ`, `p.mode = P.mode` (the inlet of the frozen growing pair, 2048-2049,
2347-2358). -/
def NearDeltaBoundC : Prop :=
  ∀ P : PlanarData, IsPlanarReference P → ∀ Kset : Set ℝ, IsCompact Kset →
    Kset ⊆ Ioo 0 (1 / 4) → ∀ mZ : ℝ, 3 / 2 < mZ → ∀ dm dp : ℝ, 0 < dm →
    ∃ K : ℕ, ∀ a b δ m0 Dp : ℝ, 0 < a → 0 < b → b < 1 → 0 < δ → 0 < m0 → m0 < 3 * dm / 11 →
      0 < Dp → ∀ (C0 : ℝ) (k0 : ℕ), 0 < C0 → ∀ Sig : ℝ, 0 < Sig →
    ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < ν₀ ∧
      ∀ (p : Params) (d : ℝ), UnforcedLeray.Short.IIb.BgRegime p d dm dp → p.ν ≤ ν₀ →
      p.ageCut = Sig → p.mode = P.mode →
      ∀ (S_in : ℝ) (V rb : ℝ → UnforcedLeray.SpatialField),
        UnforcedLeray.Short.IIb.ExactSplitII p (UnforcedLeray.Short.IIb.rhoB p m0 C0 k0) S_in V rb →
        S_in ≤ p.ε ^ (-b) →
      ∀ μ ∈ Kset, ∀ o : NearOps p.c mZ (UnforcedLeray.Short.IIb.rhoB p m0 C0 k0),
        IsActualNear p V rb μ δ (p.ε ^ (-b)) o →
        ‖conjG (gainEquiv p.c mZ (UnforcedLeray.Short.IIb.rhoB p m0 C0 k0) P.eigenvalue.re p.ν_pos)
            (o.DN - o.D0)‖ ≤
          C * p.ν⁻¹ ^ k * deltaNRhs a b K (etaDelta P.eigenvalue.re δ) m0 Dp p.ε p.ν

/-- **`near:masked-free-bound`** (source 4023-4031): the complete blocks with free energy, the positive
partial-strip bounds and the two end regions give `‖g⁻¹S_N g‖_{H_T → H} ≤ P_ν e^{η_δ/ν}`; on `Z`
(`‖F₁ + F₂‖_{H_T} ≤ ‖F‖_Z` for `W ≥ 1`, `ρ_b ≤ 1`). -/
def NearMaskedFreeBoundC : Prop :=
  ∀ P : PlanarData, IsPlanarReference P → ∀ Kset : Set ℝ, IsCompact Kset →
    Kset ⊆ Ioo 0 (1 / 4) → ∀ mZ : ℝ, 0 ≤ mZ → ∀ dm dp : ℝ, 0 < dm →
    ∀ b δ : ℝ, 0 < b → b < 1 → 0 < δ →
    ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < ν₀ ∧
      ∀ (p : Params) (d : ℝ), UnforcedLeray.Short.IIb.BgRegime p d dm dp → p.ν ≤ ν₀ →
      ∀ ρb : ℝ, 0 < ρb → ρb ≤ 1 → ∀ μ ∈ Kset, ∀ SN : Zsp p.c mZ ρb →L[ℝ] Hsp p.c,
        IsMaskedNear p μ δ (p.ε ^ (-b)) SN →
        ‖gainConjS P.eigenvalue.re p.ν_pos SN‖ ≤
          C * p.ν⁻¹ ^ k * Real.exp (etaDelta P.eigenvalue.re δ / p.ν)

/-- **The near solver under the parameter choice** (source 3943-3951 `near:inverse-comparison`,
4109-4124, 4023-4031; the near clauses of `PairNormAndNearSolver`, 5540-5547).  With `K` the integer
of `near:deltaN`, `K(a+b) < 1/100`, `θ = min{a/2, b/2, 1/100, 3/22}`, `d₀ = γ/3`, `η_δ, m₀ < θd₀/8`,
`D_⊥ > η_δ + θd₀`, and `ε = C_* ν^r e^{-d₀/ν}` (`C_* ∈ [c₁, c₂]`, `|r| ≤ r_max`): `D₀` and `D_N` are
units, `‖G⁻¹D_N⁻¹G‖ ≤ P_ν`, `‖G⁻¹(D_N⁻¹ - D₀⁻¹)G‖ ≤ P_ν e^{-θd₀/(2ν)}` and
`‖g⁻¹S_N g‖ ≤ P_ν e^{η_δ/ν}`.  The slow age `Σ > 0` of the inlet is fixed before the constants,
at the levels with `p.ageCut = Σ`, `p.mode = P.mode` (2048-2049, 2347-2358). -/
def NearSolverC : Prop :=
  ∀ P : PlanarData, IsPlanarReference P → ∀ Kset : Set ℝ, IsCompact Kset →
    Kset ⊆ Ioo 0 (1 / 4) → ∀ mZ : ℝ, 3 / 2 < mZ → ∀ dm dp : ℝ, 0 < dm →
    ∃ K : ℕ, ∀ a b δ m0 Dp : ℝ, 0 < a → 0 < b → b < 1 → (K : ℝ) * (a + b) < 1 / 100 → 0 < δ →
      0 < m0 → m0 < 3 * dm / 11 →
      etaDelta P.eigenvalue.re δ < thetaAB a b * (P.eigenvalue.re / 3) / 8 →
      m0 < thetaAB a b * (P.eigenvalue.re / 3) / 8 →
      etaDelta P.eigenvalue.re δ + thetaAB a b * (P.eigenvalue.re / 3) < Dp →
      ∀ (C0 : ℝ) (k0 : ℕ), 0 < C0 → ∀ c₁ c₂ rmax : ℝ, 0 < c₁ → c₁ ≤ c₂ → 0 ≤ rmax →
      ∀ Sig : ℝ, 0 < Sig →
    ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < ν₀ ∧
      ∀ (p : Params) (d : ℝ), UnforcedLeray.Short.IIb.BgRegime p d dm dp → p.ν ≤ ν₀ →
      p.ageCut = Sig → p.mode = P.mode →
      (∃ Cs ∈ Icc c₁ c₂, ∃ r ∈ Icc (-rmax) rmax,
        p.ε = Cs * p.ν ^ r * Real.exp (-(P.eigenvalue.re / 3) / p.ν)) →
      ∀ (S_in : ℝ) (V rb : ℝ → UnforcedLeray.SpatialField),
        UnforcedLeray.Short.IIb.ExactSplitII p (UnforcedLeray.Short.IIb.rhoB p m0 C0 k0) S_in V rb →
        S_in ≤ p.ε ^ (-b) →
      ∀ μ ∈ Kset, ∀ o : NearOps p.c mZ (UnforcedLeray.Short.IIb.rhoB p m0 C0 k0),
        IsActualNear p V rb μ δ (p.ε ^ (-b)) o →
        IsUnit o.D0 ∧ IsUnit o.DN ∧
          ‖conjG (gainEquiv p.c mZ (UnforcedLeray.Short.IIb.rhoB p m0 C0 k0) P.eigenvalue.re
              p.ν_pos) (Ring.inverse o.DN)‖ ≤ C * p.ν⁻¹ ^ k ∧
          ‖conjG (gainEquiv p.c mZ (UnforcedLeray.Short.IIb.rhoB p m0 C0 k0) P.eigenvalue.re
              p.ν_pos) (Ring.inverse o.DN - Ring.inverse o.D0)‖ ≤
            C * p.ν⁻¹ ^ k * Real.exp (-(thetaAB a b * (P.eigenvalue.re / 3)) / (2 * p.ν)) ∧
          ‖gainConjS P.eigenvalue.re p.ν_pos o.SN‖ ≤
            C * p.ν⁻¹ ^ k * Real.exp (etaDelta P.eigenvalue.re δ / p.ν)

/-- **Real forms of the body inverses** (source 1675-1677): at every level of the regime and real
`μ ∈ K ⋐ (0, 1/4)`, the curved body inverse `T_ε = (μ - A_ε)^{-1}P_ε` (`PartIIa.Teps`, `P = 2εc`) and
the flat one `T_0` (`PartIIa.T0flat`) preserve real fields: they have real forms `R_ε, R_0 : H → H`. -/
def BodyRealForms : Prop :=
  ∀ Kset : Set ℝ, IsCompact Kset → Kset ⊆ Ioo 0 (1 / 4) → ∀ dm dp : ℝ, 0 < dm →
    ∃ ν₀ : ℝ, 0 < ν₀ ∧
      ∀ (p : Params) (d : ℝ), UnforcedLeray.Short.IIb.BgRegime p d dm dp → p.ν ≤ ν₀ →
      ∀ μ ∈ Kset,
        (∃ R : Hsp p.c →L[ℝ] Hsp p.c, IsBodyTransport R
          (UnforcedLeray.Short.PartIIa.Teps (P := p.period) p.ν_pos p.ε_pos p.c_pos rfl (μ : ℂ))) ∧
        (∃ R : Hsp p.c →L[ℝ] Hsp p.c, IsBodyTransport R
          (UnforcedLeray.Short.PartIIa.T0flat p.c_pos p.ν (μ : ℂ)))

/-- **The forced column** (source 4079-4132): with the body inverses `R_ε, R_0` (real forms of
`T_ε, T_0`), `u_ε = M_U R_ε f`, `u₀ = M₀R₀f`, `T_ε = D_N⁻¹u_ε`, `T₀ = D₀⁻¹u₀`, under the hypotheses of
`NearSolverC` there is a fixed `c' > 0` with `‖g⁻¹(T_ε - T₀)‖_Z ≤ P_ν e^{-c'/ν}‖f‖_H` for every body
source `f ∈ H` (the input carries no gain, 4116-4118).  This is the near input of
`CurvedFlatComparison` (5896-5899).  The slow age `Σ > 0` of the inlet is fixed before the
constants, at the levels with `p.ageCut = Σ`, `p.mode = P.mode` (2048-2049, 2347-2358). -/
def ForcedColumnC : Prop :=
  ∀ P : PlanarData, IsPlanarReference P → ∀ Kset : Set ℝ, IsCompact Kset →
    Kset ⊆ Ioo 0 (1 / 4) → ∀ mZ : ℝ, 3 / 2 < mZ → ∀ dm dp : ℝ, 0 < dm →
    ∃ K : ℕ, ∀ a b δ m0 Dp : ℝ, 0 < a → 0 < b → b < 1 → (K : ℝ) * (a + b) < 1 / 100 → 0 < δ →
      0 < m0 → m0 < 3 * dm / 11 →
      etaDelta P.eigenvalue.re δ < thetaAB a b * (P.eigenvalue.re / 3) / 8 →
      m0 < thetaAB a b * (P.eigenvalue.re / 3) / 8 →
      etaDelta P.eigenvalue.re δ + thetaAB a b * (P.eigenvalue.re / 3) < Dp →
      ∀ (C0 : ℝ) (k0 : ℕ), 0 < C0 → ∀ c₁ c₂ rmax : ℝ, 0 < c₁ → c₁ ≤ c₂ → 0 ≤ rmax →
      ∀ Sig : ℝ, 0 < Sig →
    ∃ (c' C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < c' ∧ 0 < ν₀ ∧
      ∀ (p : Params) (d : ℝ), UnforcedLeray.Short.IIb.BgRegime p d dm dp → p.ν ≤ ν₀ →
      p.ageCut = Sig → p.mode = P.mode →
      (∃ Cs ∈ Icc c₁ c₂, ∃ r ∈ Icc (-rmax) rmax,
        p.ε = Cs * p.ν ^ r * Real.exp (-(P.eigenvalue.re / 3) / p.ν)) →
      ∀ (S_in : ℝ) (V rb : ℝ → UnforcedLeray.SpatialField),
        UnforcedLeray.Short.IIb.ExactSplitII p (UnforcedLeray.Short.IIb.rhoB p m0 C0 k0) S_in V rb →
        S_in ≤ p.ε ^ (-b) →
      ∀ μ ∈ Kset, ∀ o : NearOps p.c mZ (UnforcedLeray.Short.IIb.rhoB p m0 C0 k0),
        IsActualNear p V rb μ δ (p.ε ^ (-b)) o →
      ∀ Reps R0 : Hsp p.c →L[ℝ] Hsp p.c,
        IsBodyTransport Reps
          (UnforcedLeray.Short.PartIIa.Teps (P := p.period) p.ν_pos p.ε_pos p.c_pos rfl (μ : ℂ)) →
        IsBodyTransport R0 (UnforcedLeray.Short.PartIIa.T0flat p.c_pos p.ν (μ : ℂ)) →
        ∀ f : Hsp p.c,
          ‖(gainEquiv p.c mZ (UnforcedLeray.Short.IIb.rhoB p m0 C0 k0) P.eigenvalue.re p.ν_pos).symm
              (Ring.inverse o.DN (o.MU (Reps f)) - Ring.inverse o.D0 (o.M0 (R0 f)))‖ ≤
            C * p.ν⁻¹ ^ k * Real.exp (-c' / p.ν) * ‖f‖

/-- **The pinned near operators exist** (assembly of `FreeStressExists`, `MaskedNearExists`,
`CoeffMultExists`, `FlatTrainMultBound`, `SplitMultBound`): at every level of the regime with
`ν ≤ ν₀`, every exact split with `ρ_b = rhoB p m₀ C₀ k₀`, and `μ ∈ K`, there are operators with
`IsActualNear p V r_b μ δ ε^{-b}`.  The slow age `Σ > 0` of the inlet is fixed before `ν₀`, at the
levels with `p.ageCut = Σ`, `p.mode = P.mode` (2048-2049, 2347-2358; the split multiplier needs
the coefficient bound of `SplitMultBound`). -/
def NearOpsExistC : Prop :=
  ∀ P : PlanarData, IsPlanarReference P → ∀ Kset : Set ℝ, IsCompact Kset →
    Kset ⊆ Ioo 0 (1 / 4) → ∀ mZ : ℝ, 3 / 2 < mZ → ∀ dm dp : ℝ, 0 < dm →
    ∀ b δ m0 : ℝ, 0 < b → b < 1 → 0 < δ → 0 < m0 → m0 ≤ 3 * dm / 11 →
    ∀ (C0 : ℝ) (k0 : ℕ), 0 < C0 → ∀ Sig : ℝ, 0 < Sig → ∃ ν₀ : ℝ, 0 < ν₀ ∧
      ∀ (p : Params) (d : ℝ), UnforcedLeray.Short.IIb.BgRegime p d dm dp → p.ν ≤ ν₀ →
      p.ageCut = Sig → p.mode = P.mode →
      ∀ (S_in : ℝ) (V rb : ℝ → UnforcedLeray.SpatialField),
        UnforcedLeray.Short.IIb.ExactSplitII p (UnforcedLeray.Short.IIb.rhoB p m0 C0 k0) S_in V rb →
      ∀ μ ∈ Kset, ∃ o : NearOps p.c mZ (UnforcedLeray.Short.IIb.rhoB p m0 C0 k0),
        IsActualNear p V rb μ δ (p.ε ^ (-b)) o

end UnforcedLeray.Short.PartIIIb.NearInst
