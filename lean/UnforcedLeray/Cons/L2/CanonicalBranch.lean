import UnforcedLeray.Cons.C01ReferenceChoice
import UnforcedLeray.Lib.PlanarSpectralB.AdjointDomain
import UnforcedLeray.Infra.AnalyticFredholm.FiniteRank
import UnforcedLeray.Cons.L2.CanonicalBranch.Bridge
import UnforcedLeray.Cons.L2.CanonicalBranch.Limit
import UnforcedLeray.Cons.L2.CanonicalBranch.Amplitude

/-!
# Target C01-G3b: the canonical branch (`CanonicalBranchHyp`)

`paper/main.tex`, Theorem G3b (`thm:ref-canonical-branch`, statement lines 735–760, proof lines
1750–1890); blueprint units B0125 (G3b), B0118 (`eq:st18-t00096`, Cauchy property and the limit on
`θ ≥ b₀`), B0119 (`eq:st18-t00097`–`t00098`, backward continuation and its bound), B0120
(`eq:st18-t00099`, exact preparation), B0124 (`eq:st18-t00102`, derivative budget and smoothness),
with the inputs B0116 (`eq:st18-t00093`), B0117 (`eq:st18-t00094`), B0112 (complement decay
`eq:st18-t00078` on `QX_G`), B0099 (G3a), B0012, B0094, B0123.

## The concrete objects

For a whole-line Rayleigh mode `(c, F)` (`WholeLineData`, the O8 output used by
`Cons/C01ReferenceChoice`): `λ = -2ic` (`lamMode`), `q = h = modeVort c F` as an element of
B0010's `X_G` (`qMode`), and `κ = ⟨Dq, q†⟩_{X_G}` with the explicit normalized adjoint
`q† = adjointMode c F` (`kapMode`, `eq:st18-t00012`). The evolution is the concrete backward
evolution `S(θ, θ')` of `-∂_θV = (L₀ + θ⁻¹D)V` (`Cons/L2/CanonicalBranch/Evolution.lean`: the Dyson
series of B0123's `e^{aD}` perturbed by B0012's `L₀`), and the normalized states
`Y_R(θ) = e^{λθ}θ^κ e^{-λR}R^{-κ} S(θ, R)q` (`stateY`, `eq:st18-t00095`) and the normalized
evolution `N(θ, θ') = e^{λθ}θ^κ S(θ, θ') e^{-λθ'}θ'^{-κ}` (`normProp`) are those of
`Cons/L2/CanonicalBranch/Limit.lean`.

## What is proved

* `S`: composition law, the energy bound `‖S(θ, θ')‖ ≤ e^{‖L₀‖(θ' - θ)}` (`eq:st18-t00098`),
  Duhamel form, strong continuity (`Evolution.lean`, no hypothesis; includes the strong
  continuity of B0123's `e^{aD}`).
* B0116 and B0117's propagation of differences from the inequalities `eq:st18-t00094`, by
  Gronwall on the running maximum (`Amplitude.lean`: `relativeGrowth_of_bounds`,
  `uniformPropagation_of_bounds`).
* B0118 from B0116 and B0117: the Cauchy estimate `eq:st18-t00096` (`cauchy_bound`), the limit
  `Y_can`, the bound `‖Y_can(θ) - q‖ ≤ C/θ`, the mild equation of the limit.
* B0119: the continuation of `V_can` below `b₀` by `S`, the mild equation on `(0, ∞)`, the bound
  `eq:st18-t00098`, continuity into `X_G` (`Limit.lean`).
* B0120: exact preparation `S(θ, R)q_R = e^{λR}R^κV_can(θ)` and `q_R = q + O(R⁻¹)`.
* The bridge between B0010's `X_G` and the blueprint's profiles (`Bridge.lean`).
* `relativeGrowthHyp_of_arbitraryData`, `uniformPropagationHyp_of_arbitraryData`, and
  **`canonicalBranchHyp_of_arbitraryData`**: `CanonicalBranchHyp` from the two named hypotheses
  below (`canonicalBranchHyp_of_parts` is the same from the intermediate statements
  `RelativeGrowthHyp`, `UniformPropagationHyp`, which are proved here from `ArbitraryDataHyp`).

## The named hypotheses (what is missing)

* `ArbitraryDataHyp` — B0117 (`eq:st18-t00094`, lines 1792–1803): the two displayed inequalities
  for the concrete amplitude `A(t) = ℓ(N(R - t, R)f)` and complement `r(t) = Q(N(R - t, R)f)`,
  `ℓ = ⟨·, q†⟩_{X_G}`, for every datum `f ∈ X_G` and every `θ = R - t ≥ b₀`. Its proof needs
  B0115 (`eq:st18-t00090`, the exact amplitude–complement system in mild form, from
  `ℓ(L₀f) = λℓ(f)` and `q† ∈ 𝒟(D)`) and B0112 (`eq:st18-t00078`, the uniform small-diffusion
  complement decay on `QX_G`, the deep input: compact Duhamel B0104 and the block iteration).
* `ClassicalRegularityHyp` — B0124 (`eq:st18-t00102`, lines 1879–1888: "The local argument gives
  smoothness for positive `θ`") together with the identification of `D` and `L₀` with their
  classical formulas: every mild solution of the concrete backward evolution on `(0, ∞)` has a
  representative jointly smooth in `(θ, r)` that solves `-∂_θV = (L₀ + θ⁻¹D)V` pointwise, with
  the blueprint's classical `generatorL0` and `oscillatorD`. It is stated for every mild solution
  on `(0, ∞)`: the local smoothing argument of lines 1879–1886 does not use the asymptotics.

Not covered (not part of `CanonicalBranchHyp`): the derivative budget
`‖q_R‖_{X_{G,j}} ≤ C_j(1 + R)^{j/2}` (`eq:st18-t00015`, second clause; B0124).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Cons.G3b

open UnforcedLeray.B0010 Blueprint.Planar ComplexODEC UnforcedLeray.Cons.C01

/-! ## The concrete reference data of a whole-line mode -/

/-- `λ = -2ic` (G1, `eq:st18-t00008`, through the whole-line mode of O8). -/
def lamMode (c : ℂ) : ℂ := -2 * Complex.I * c

/-- `κ = ℓ(Dq) = ⟨Dq, q†⟩_{X_G}` with the explicit normalized adjoint `q† = Gū/J̄`
(`eq:st18-t00012`, `eq:st18-t00066`). -/
def kapMode (c : ℂ) (F : ℝ → ℂ) : ℂ :=
  gaussianPairing (oscillatorD (modeVort c F)) (adjointMode c F)

/-- The eigenvector `q = h(r)e^{2iϑ}` (G1) as an element of B0010's `X_G`. -/
def qMode {c : ℂ} {F : ℝ → ℂ} (hF : WholeLineData c F) : XG :=
  (memLp_of_memXG (memXG_modeVort hF)).toLp (modeVort c F)

theorem coeFn_qMode {c : ℂ} {F : ℝ → ℂ} (hF : WholeLineData c F) :
    (qMode hF : ℝ → ℂ) =ᵐ[xGMeasure] modeVort c F :=
  MemLp.coeFn_toLp _

/-- The normalized adjoint eigenvector `q† = Gū/J̄` (`eq:st18-t00066`; `adjointMode`, G3a) as an
element of B0010's `X_G`; `ℓ = ⟨·, q†⟩_{X_G}` is `f ↦ ⟪q†, f⟫`. -/
def qdagMode {c : ℂ} {F : ℝ → ℂ} (hF : WholeLineData c F) : XG :=
  (memLp_of_memXG (memXG_adjointMode hF)).toLp (adjointMode c F)

/-- The explicit normalized adjoint belongs to the closed oscillator domain. The proof uses its
smooth angular-two Gaussian representative, which is a.e. equal to the literal radial formula. -/
theorem qdagMode_D_action {c : ℂ} {F : ℝ → ℂ} (hF : WholeLineData c F) :
    ∃ hD : qdagMode hF ∈ B0094.D.domain, ∃ DF : XG,
      B0094.D ⟨qdagMode hF, hD⟩ = DF := by
  obtain ⟨β₀, hβ₀, hβ⟩ := exists_mode_eq_regLog hF
  have hβ' : ∀ t, F t = β₀ * regLog c t := fun t => (hβ t).1
  let J : ℂ := directAdjointPairing c F
  have hJ : J ≠ 0 := by simpa [J] using directAdjointPairing_ne_zero hF
  let f₂ : Profile := fun r => (r : ℂ) ^ 2 *
    PlanarSpectral.adjointBeta c β₀ J (r ^ 2)
  have hadj : adjointMode c F =ᵐ[xGMeasure] f₂ := by
    filter_upwards [PlanarSpectral.adjointProfileFormula_ae_eq_adjointBeta hβ' hJ]
      with r hr
    simpa [f₂, adjointMode, adjointKernel, PlanarSpectral.adjointProfileFormula,
      J, directAdjointPairing] using hr
  let hm := memLp_of_memXG (memXG_adjointMode hF)
  obtain ⟨hD, DF, hDact, df, hfield, hdf⟩ :=
    PlanarSpectral.exists_Ddomain_of_gaussClass_profile_ae hadj
      (PlanarSpectral.gaussClass_adjointBeta hF β₀ J)
      (PlanarSpectral.isAngularTwo_angularTwoField_radialSq
        (PlanarSpectral.adjointBeta c β₀ J)) hm
  exact ⟨hD, DF, hDact⟩

/-- The explicit normalized adjoint belongs to the closed oscillator domain. -/
theorem qdagMode_mem_Ddomain {c : ℂ} {F : ℝ → ℂ} (hF : WholeLineData c F) :
    qdagMode hF ∈ B0094.D.domain := by
  obtain ⟨hD, DF, hDact⟩ := qdagMode_D_action hF
  exact hD

theorem inner_qdagMode_qMode {c : ℂ} {F : ℝ → ℂ} (hF : WholeLineData c F) :
    inner ℂ (qdagMode hF) (qMode hF) = 1 := by
  rw [qdagMode, qMode, ← gaussianPairing_eq_inner (memXG_modeVort hF) (memXG_adjointMode hF)]
  exact gaussianPairing_modeVort_adjointMode (directAdjointPairing_ne_zero hF)

/-- The blueprint's classical radial formula for `L₀` is the profile formula underlying the
bounded operator `B0012.L0`. -/
theorem generatorL0_eq_L0Fun (f : Profile) (r : ℝ) :
    generatorL0 f r = B0012.L0Fun f r := by
  rw [Blueprint.Planar.generatorL0, B0012.L0Fun, vortexOmega_eq, strainK_eq,
    greenInverse_eq_R]

/-- The explicit adjoint mode makes the amplitude functional a left eigenfunctional of the
concrete bounded Gaussian operator `L₀` on all of `X_G` (`eq:st18-t00066`). -/
theorem inner_qdagMode_L0 {c : ℂ} {F : ℝ → ℂ} (hF : WholeLineData c F) (f : XG) :
    inner ℂ (qdagMode hF) (B0012.L0 f) =
      lamMode c * inner ℂ (qdagMode hF) f := by
  let p : Profile := (f : ℝ → ℂ)
  have hpMeas : AEStronglyMeasurable p (volume.restrict (Ioi (0 : ℝ))) :=
    (Lp.aestronglyMeasurable f).mono_ac B0012.restrict_ac
  have hp : MemXG p := memXG_of_memLp hpMeas (Lp.memLp f)
  have hgenAe : generatorL0 p =ᵐ[xGMeasure] (B0012.L0 f : ℝ → ℂ) := by
    filter_upwards [B0012.coeFn_L0 f] with r hr
    rw [show generatorL0 p r = B0012.L0Fun p r from generatorL0_eq_L0Fun p r]
    simpa [p] using hr.symm
  have hgenLp : MemLp (generatorL0 p) 2 xGMeasure :=
    (Lp.memLp (B0012.L0 f)).ae_eq hgenAe.symm
  have hgenMeas : AEStronglyMeasurable (generatorL0 p)
      (volume.restrict (Ioi (0 : ℝ))) :=
    (B0012.memXG_coe (B0012.L0 f)).1.congr (B0012.restrict_ac.ae_le hgenAe.symm)
  have hgen : MemXG (generatorL0 p) := memXG_of_memLp hgenMeas hgenLp
  have hq : MemXG (adjointMode c F) := memXG_adjointMode hF
  have hpRep : (memLp_of_memXG hp).toLp p = f := by
    apply Lp.ext
    filter_upwards [(memLp_of_memXG hp).coeFn_toLp] with r hr
    simpa [p] using hr
  have hgenRep : (memLp_of_memXG hgen).toLp (generatorL0 p) = B0012.L0 f := by
    apply Lp.ext
    filter_upwards [(memLp_of_memXG hgen).coeFn_toLp, B0012.coeFn_L0 f] with r hr₁ hr₂
    rw [hr₁, generatorL0_eq_L0Fun]
    exact hr₂.symm
  have hleft := (isAdjointEigenvector_adjointMode hF
    (directAdjointPairing_ne_zero hF)).left_eigen p hp
  rw [gaussianPairing_eq_inner hp hq, gaussianPairing_eq_inner hgen hq,
    hgenRep, hpRep] at hleft
  simpa [qdagMode, lamMode] using hleft

/-- The whole-line eigenmode representative also belongs to the closed oscillator domain. -/
theorem qMode_mem_Ddomain {c : ℂ} {F : ℝ → ℂ} (hF : WholeLineData c F) :
    qMode hF ∈ B0094.D.domain := by
  have hmode := PlanarSpectral.modeVort_mem_Ddomain hF
  have hrep : (memLp_modeVort_XG hF).toLp (modeVort c F) = qMode hF := by
    apply Lp.ext
    filter_upwards [(memLp_modeVort_XG hF).coeFn_toLp,
      (memLp_of_memXG (memXG_modeVort hF)).coeFn_toLp] with r hr₁ hr₂
    exact hr₁.trans hr₂.symm
  rw [← hrep]
  exact hmode

/-- The bounded cross maps `PD` and `DP` from H4 are concrete compact rank-one operators once
both canonical modes lie in `D(D)`. Their operator norms are finite because they are continuous
linear maps. -/
theorem exists_compact_cross_maps {c : ℂ} {F : ℝ → ℂ} (hF : WholeLineData c F) :
    ∃ PD DP : XG →L[ℂ] XG,
      (∀ f : B0094.D.domain,
        PD f = inner ℂ (qdagMode hF) (B0094.D f) • qMode hF) ∧
      (∀ x : XG,
        DP x = inner ℂ (qdagMode hF) x •
          B0094.D ⟨qMode hF, qMode_mem_Ddomain hF⟩) ∧
      IsCompactOperator PD ∧ IsCompactOperator DP ∧ 0 ≤ ‖PD‖ ∧ 0 ≤ ‖DP‖ := by
  let qdD : B0094.D.domain := ⟨qdagMode hF, qdagMode_mem_Ddomain hF⟩
  let qD : B0094.D.domain := ⟨qMode hF, qMode_mem_Ddomain hF⟩
  let ψPD := innerSL ℂ (B0094.D qdD)
  let ψP := innerSL ℂ (qdagMode hF)
  let PD := UnforcedLeray.Infra.Dunford.rankOneProj ψPD (qMode hF)
  let DP := UnforcedLeray.Infra.Dunford.rankOneProj ψP (B0094.D qD)
  have hPD : ∀ f : B0094.D.domain,
      PD f = inner ℂ (qdagMode hF) (B0094.D f) • qMode hF := by
    intro f
    change inner ℂ (B0094.D qdD) (f : XG) • qMode hF = _
    rw [B0094.D_symm qdD f]
  have hDP : ∀ x : XG,
      DP x = inner ℂ (qdagMode hF) x •
        B0094.D ⟨qMode hF, qMode_mem_Ddomain hF⟩ := by
    intro x
    simp [DP, ψP, qD, UnforcedLeray.Infra.Dunford.rankOneProj_apply,
      innerSL_apply_apply]
  have hPDc : IsCompactOperator PD := by
    change IsCompactOperator (ψPD.smulRight (qMode hF))
    exact UnforcedLeray.Infra.AnalyticFredholm.isCompactOperator_smulRight ψPD _
  have hDPc : IsCompactOperator DP := by
    change IsCompactOperator (ψP.smulRight (B0094.D qD))
    exact UnforcedLeray.Infra.AnalyticFredholm.isCompactOperator_smulRight ψP _
  exact ⟨PD, DP, hPD, hDP, hPDc, hDPc, norm_nonneg _, norm_nonneg _⟩

/-- The eigenvorticity representative is a right eigenvector of the concrete Gaussian operator. -/
theorem L0_qMode {c : ℂ} {F : ℝ → ℂ} (hF : WholeLineData c F) :
    B0012.L0 (qMode hF) = lamMode c • qMode hF := by
  let hm := memLp_of_memXG (memXG_modeVort hF)
  rw [qMode, B0012.L0_toLp hm]
  apply Lp.ext
  filter_upwards [B0012.ae_xG_pos, (B0012.memLp_L0Fun hm).coeFn_toLp,
    hm.coeFn_toLp, Lp.coeFn_smul (lamMode c) (qMode hF)] with r hr hL hq hsmul
  have hq' : ((qMode hF : XG) : ℝ → ℂ) r = modeVort c F r := by
    simpa only [qMode, hm] using hq
  rw [hL]
  change B0012.L0Fun (modeVort c F) r =
    ((lamMode c • qMode hF : XG) : ℝ → ℂ) r
  rw [hsmul, Pi.smul_apply, smul_eq_mul, hq', ← generatorL0_eq_L0Fun (modeVort c F) r,
    generatorL0_modeVort hF hr]
  simp [lamMode]

/-- The normalized rank-one complement commutes with `L₀`, since `q` and its amplitude are
right and left eigenvectors for the same eigenvalue. -/
theorem projQ_L0_commute {c : ℂ} {F : ℝ → ℂ} (hF : WholeLineData c F) (f : XG) :
    projQ (qMode hF) (qdagMode hF) (B0012.L0 f) =
      B0012.L0 (projQ (qMode hF) (qdagMode hF) f) := by
  rw [projQ, inner_qdagMode_L0 hF, projQ, map_sub, map_smul, L0_qMode hF]
  module

/-! ## The named hypotheses -/

/-- **B0116, `eq:st18-t00093`** (`paper/main.tex` lines 1768–1790; uniform relative growth up to
long turnover times), for the reference data of a whole-line mode: there are `b₀ > 0` and `C`,
independent of `R` and `θ`, with `‖Y_R(θ) - q‖ ≤ C/θ` for `b₀ ≤ θ ≤ R`, where
`Y_R(θ) = e^{λθ}θ^κV_R(θ)`, `V_R(θ) = e^{-λR}R^{-κ}W_R(R - θ)` (`eq:st18-t00095`) and `W_R` is the
forward solution of `eq:st18-t00088` from `q`. In the manuscript `Y_R(θ) = A(t)q + r(t)` and
`|A(t) - 1| + ‖r(t)‖ ≤ C/θ`. Proof dependencies: B0115 (`eq:st18-t00090`), B0112
(`eq:st18-t00078`), B0097; Gronwall (INF30). -/
def RelativeGrowthHyp : Prop :=
  ∀ (c : ℂ) (F : ℝ → ℂ) (hF : WholeLineData c F), ∃ b₀ C : ℝ, 0 < b₀ ∧
    ∀ θ R : ℝ, b₀ ≤ θ → θ ≤ R →
      ‖stateY (lamMode c) (kapMode c F) (qMode hF) R θ - qMode hF‖ ≤ C / θ

/-- **B0117, `eq:st18-t00094`** (`paper/main.tex` lines 1792–1803; arbitrary-data inequalities):
"These inequalities also prove uniform propagation of differences in the normalized state
`Aq + r`, on every interval `θ ≥ b₀`." For the reference data of a whole-line mode: there are
`b₀ > 0` and `C` with `‖N(θ, θ')‖ ≤ C` for `b₀ ≤ θ ≤ θ'`, where
`N(θ, θ')f = e^{λθ}θ^κ S(θ, θ')(e^{-λθ'}θ'^{-κ}f)` is the normalized state at `θ` of the solution
whose normalized state at `θ'` is `f` (`A(0) = ℓf`, `r(0) = Qf`). Proof dependencies: B0115,
B0116, B0112; Gronwall. -/
def UniformPropagationHyp : Prop :=
  ∀ (c : ℂ) (F : ℝ → ℂ), WholeLineData c F → ∃ b₀ C : ℝ, 0 < b₀ ∧
    ∀ θ θ' : ℝ, b₀ ≤ θ → θ ≤ θ' → ‖normProp (lamMode c) (kapMode c F) θ θ'‖ ≤ C

/-- **B0117, `eq:st18-t00094`** (`paper/main.tex` lines 1792–1803; arbitrary-data inequalities),
for the reference data of a whole-line mode: there are `b₀ > 0`, `C ≥ 0`, `g ≥ 0` such that for
every datum `f ∈ X_G` at `R` and every `t ≥ 0` with `θ = R - t ≥ b₀`, the amplitude
`A(t) = ℓ(N(θ, R)f)` and complement `r(t) = Q(N(θ, R)f)` of the normalized state
(`eq:st18-t00089`, `ℓ = ⟨·, q†⟩_{X_G}`, `Q = I - qℓ`) satisfy
`‖r(t)‖ ≤ Ce^{-gt}‖Qf‖ + Cβ(t)sup_{s≤t}|A(s)|` and
`|A(t) - ℓf| ≤ Cβ(t)‖Qf‖ + C∫₀^tβ(s)²sup_{u≤s}|A(u)|ds`, `β(t) = 1/(R - t)`
(`ArbitraryDataBounds`). Proof dependencies: B0115 (`eq:st18-t00090`), B0112
(`eq:st18-t00078`), B0097, B0099 (`ℓD` bounded). -/
def ArbitraryDataHyp : Prop :=
  ∀ (c : ℂ) (F : ℝ → ℂ) (hF : WholeLineData c F), ∃ b₀ C g : ℝ, 0 < b₀ ∧ 0 ≤ C ∧ 0 ≤ g ∧
    ArbitraryDataBounds (lamMode c) (kapMode c F) (qMode hF) (qdagMode hF) b₀ C g

/-- B0116 from B0117's inequalities (Gronwall, lines 1777–1790). -/
theorem relativeGrowthHyp_of_arbitraryData (h : ArbitraryDataHyp) : RelativeGrowthHyp := by
  intro c F hF
  obtain ⟨b₀, C, g, hb₀, hC, -, hB⟩ := h c F hF
  obtain ⟨K, hK⟩ := relativeGrowth_of_bounds hb₀ hC hB (inner_qdagMode_qMode hF)
  exact ⟨b₀, K, hb₀, hK⟩

/-- B0117's uniform propagation of differences from its inequalities (Gronwall, line 1803). -/
theorem uniformPropagationHyp_of_arbitraryData (h : ArbitraryDataHyp) :
    UniformPropagationHyp := by
  intro c F hF
  obtain ⟨b₀, C, g, hb₀, hC, hg, hB⟩ := h c F hF
  obtain ⟨K, hK⟩ := uniformPropagation_of_bounds hb₀ hC hg hB
  exact ⟨b₀, K, hb₀, hK⟩

/-- **B0124 with the classical reading of G3b** (`paper/main.tex` line 745, "smooth at every
positive `θ`"; lines 1879–1888, `eq:st18-t00102`: "The local argument gives smoothness for
positive `θ`"; the classical formulas of `L₀` (B0012, `eq:st18-t00006`) and of
`D = Δ + ½y·∇ + 2` (B0093, B0094, `eq:st18-t00011`)): every mild solution `V` of the concrete
backward evolution on `(0, ∞)` (`V(θ) = S(θ, θ')V(θ')`, `0 < θ ≤ θ'`) has a representative `W`
(`W(θ) = V(θ)` a.e. for `θ > 0`) that is jointly smooth in `(θ, r)` on `(0, ∞)²` and solves
`-∂_θW = L₀W + θ⁻¹DW` pointwise, with the blueprint's `generatorL0` and `oscillatorD`.
Infrastructure: INF08, B0121–B0123 (graph norms, `L₀` on `X_{G,j}`, smoothing of `e^{aD}`),
Sobolev embedding. -/
def ClassicalRegularityHyp : Prop :=
  ∀ V : ℝ → XG, (∀ θ θ' : ℝ, 0 < θ → θ ≤ θ' → V θ = S θ θ' (V θ')) →
    ∃ W : ℝ → Profile, (∀ θ : ℝ, 0 < θ → W θ =ᵐ[xGMeasure] (V θ : ℝ → ℂ)) ∧
      ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => W z.1 z.2) (Ioi 0 ×ˢ Ioi 0) ∧
      ∀ θ : ℝ, 0 < θ → ∀ r : ℝ, 0 < r →
        -deriv (fun t => W t r) θ = generatorL0 (W θ) r + (θ : ℂ)⁻¹ * oscillatorD (W θ) r

/-! ## The canonical branch in `X_G` for the reference data -/

/-- **G3b in `X_G` for a whole-line mode** (B0118 with B0119, from B0116 and B0117). -/
theorem exists_isXGCanonicalBranch_mode (hG : RelativeGrowthHyp) (hN : UniformPropagationHyp)
    {c : ℂ} {F : ℝ → ℂ} (hF : WholeLineData c F) :
    ∃ V : ℝ → XG, IsXGCanonicalBranch (lamMode c) (kapMode c F) (qMode hF) V := by
  obtain ⟨b₁, C₁, -, hG'⟩ := hG c F hF
  obtain ⟨b₂, C₂, -, hN'⟩ := hN c F hF
  exact exists_isXGCanonicalBranch (b := max b₁ b₂)
    (fun θ R hθ hR => hG' θ R ((le_max_left _ _).trans hθ) hR)
    (fun θ θ' hθ h => hN' θ θ' ((le_max_right _ _).trans hθ) h)

/-! ## From `X_G` to the blueprint's profiles -/

theorem continuousOn_slice {W : ℝ → Profile}
    (hW : ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => W z.1 z.2) (Ioi 0 ×ˢ Ioi 0)) {θ : ℝ} (hθ : 0 < θ) :
    ContinuousOn (W θ) (Ioi 0) := by
  have h := hW.continuousOn.comp (Continuous.continuousOn (continuous_const.prodMk continuous_id))
    (fun r (hr : r ∈ Ioi (0 : ℝ)) => (⟨hθ, hr⟩ : ((θ, r) : ℝ × ℝ) ∈ Ioi 0 ×ˢ Ioi 0))
  exact h

/-- A smooth representative of an `X_G`-canonical branch is a blueprint canonical branch, and it
is continuous into `X_G`. -/
theorem isCanonicalBranch_of_rep {lam κ : ℂ} {q : XG} {q₀ : Profile}
    (hq : (q : ℝ → ℂ) =ᵐ[xGMeasure] q₀) {V : ℝ → XG} (hV : IsXGCanonicalBranch lam κ q V)
    {W : ℝ → Profile} (hWV : ∀ θ : ℝ, 0 < θ → W θ =ᵐ[xGMeasure] (V θ : ℝ → ℂ))
    (hWs : ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => W z.1 z.2) (Ioi 0 ×ˢ Ioi 0))
    (hWe : ∀ θ : ℝ, 0 < θ → ∀ r : ℝ, 0 < r →
      -deriv (fun t => W t r) θ = generatorL0 (W θ) r + (θ : ℂ)⁻¹ * oscillatorD (W θ) r) :
    IsCanonicalBranch lam κ q₀ W ∧ IsXGContinuous W := by
  have hmem : ∀ θ : ℝ, 0 < θ → MemXG (W θ) := fun θ hθ =>
    memXG_of_memLp ((continuousOn_slice hWs hθ).aestronglyMeasurable measurableSet_Ioi)
      ((Lp.memLp (V θ)).ae_eq (hWV θ hθ).symm)
  have hWX : IsXGContinuous W := by
    intro θ₀ hθ₀
    have hc : Tendsto (fun θ => ‖V θ - V θ₀‖) (𝓝 θ₀) (𝓝 0) := by
      have h := ((hV.continuousOn θ₀ hθ₀).continuousAt (Ioi_mem_nhds hθ₀)).tendsto
      rw [tendsto_iff_norm_sub_tendsto_zero] at h
      exact h
    refine hc.congr' ?_
    filter_upwards [Ioi_mem_nhds hθ₀] with θ hθ
    symm
    refine gaussianNorm_eq_norm ?_
    filter_upwards [hWV θ hθ, hWV θ₀ hθ₀, Lp.coeFn_sub (V θ) (V θ₀)] with r h1 h2 h3
    rw [h3, Pi.sub_apply, h1, h2]
  refine ⟨⟨hmem, hWs, hWe, ?_, ?_, hWX⟩, hWX⟩
  · obtain ⟨C, hC⟩ := hV.bounded_near_zero
    exact ⟨C, fun θ hθ hθ1 => (gaussianNorm_eq_norm (hWV θ hθ)).trans_le (hC θ hθ hθ1)⟩
  · obtain ⟨C, θ₁, hθ₁, hA⟩ := hV.asymptotic
    refine ⟨C, θ₁, hθ₁, fun θ hθ => ?_⟩
    have hθ0 : 0 < θ := hθ₁.trans_le hθ
    have hae : (fun r => Complex.exp (lam * θ) * (θ : ℂ) ^ κ * W θ r - q₀ r) =ᵐ[xGMeasure]
        ((gauge lam κ θ • V θ - q : XG) : ℝ → ℂ) := by
      filter_upwards [hWV θ hθ0, Lp.coeFn_sub (gauge lam κ θ • V θ) q,
        Lp.coeFn_smul (gauge lam κ θ) (V θ), hq] with r h1 h2 h3 h4
      rw [h2, Pi.sub_apply, h3, Pi.smul_apply, smul_eq_mul, ← h1, ← h4]
      rfl
    rw [gaussianNorm_eq_norm hae]
    exact hA θ hθ

/-! ## The target -/

/-- **G3b, the `X_G`-continuous form** (`CanonicalBranchXGHyp`), from B0116, B0117 and the
regularity statement of B0124. -/
theorem canonicalBranchXGHyp_of_parts (hG : RelativeGrowthHyp) (hN : UniformPropagationHyp)
    (hR : ClassicalRegularityHyp) : CanonicalBranchXGHyp := by
  intro c F hF
  obtain ⟨V, hV⟩ := exists_isXGCanonicalBranch_mode hG hN hF
  obtain ⟨W, hWV, hWs, hWe⟩ := hR V hV.mild
  exact ⟨W, isCanonicalBranch_of_rep (coeFn_qMode hF) hV hWV hWs hWe⟩

/-- **Target C01-G3b: `CanonicalBranchHyp`** (`thm:ref-canonical-branch`, lines 735–760, proof
1809–1890; units B0125, B0118, B0119, B0124), from the three named hypotheses
`RelativeGrowthHyp` (B0116), `UniformPropagationHyp` (B0117) and `ClassicalRegularityHyp`
(B0124). -/
theorem canonicalBranchHyp_of_parts (hG : RelativeGrowthHyp) (hN : UniformPropagationHyp)
    (hR : ClassicalRegularityHyp) : CanonicalBranchHyp :=
  canonicalBranchHyp_of_XG (canonicalBranchXGHyp_of_parts hG hN hR)

/-- **Target C01-G3b: `CanonicalBranchHyp` from the two remaining named hypotheses**
(`thm:ref-canonical-branch`, lines 735–760, proof 1750–1890; units B0125, B0116–B0120, B0124):
the arbitrary-data inequalities `eq:st18-t00094` (`ArbitraryDataHyp`, B0117, resting on B0115
and B0112) and the classical regularity of mild solutions (`ClassicalRegularityHyp`, B0124). -/
theorem canonicalBranchHyp_of_arbitraryData (hA : ArbitraryDataHyp)
    (hR : ClassicalRegularityHyp) : CanonicalBranchHyp :=
  canonicalBranchHyp_of_parts (relativeGrowthHyp_of_arbitraryData hA)
    (uniformPropagationHyp_of_arbitraryData hA) hR

end UnforcedLeray.Cons.G3b
