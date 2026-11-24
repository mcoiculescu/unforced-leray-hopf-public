import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_1Org
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.Trans
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_4
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.L8_RepairSepBridge

/-!
# `PartIII-b:C/rep/5/2/regions/org` (2): both stream transitions in the velocity gain norm

Source `the November 2 reference manuscript` 5303-5316 (the regions of the far
mask and the two stream transitions, supported on `0.8/ν < s < 1/ν`), 5317-5318 (late output
`g(s)⁻¹ ≤ e^{-4γ/(9ν)}`), 5585-5592 ("the outward stream primitive obeys the same bound. This
proves the estimate for both stream transitions as well"; Young `L^{22/19} → L²` for an actual
repair source, `P_νS^kρε^{23/11}` times its gain), 5601-5605 (late margin `23γ/99 ≥ 31γ/165`),
5687-5689; the stream cutoff and its commutators 3676-3712, 4161-4214; `sep:repair-energy`
3651-3656.

## Why a new leaf

`Sub/PartIII-b_C_rep_5_2_2Org.lean` bounds `Y = (wardOps ..).1` alone on repair sources.  `Y`
contains the young-old rectangle `-χ_yS_μχ_o` (`ward:cutoff-source`, 4203-4214), whose gain ratio
reaches `e^{γ/ν}` against `ρε^{23/11} ≍ e^{-26γ/(33ν)}`; the source bounds only `S_far + Y`.  The
split used is `ageVel = ftLEOp - χ_yS_Nχ_o + transOp` (`Sub/PartIII-b_C_rep_5_2_1Org.lean`); this
file proves the stream-transition leaf `AgeVelTransRep` (velocity bound on
`transOp = Y + χ_yS_μχ_o`) from the leaves below.

## The chain at one level (`transVelRep_level`, proved)

For `T₂ = repPart (M_Uw)`:
1. `transOp_coef_rep` (`YRepStream/Trans.lean`) with the representatives `g₁ = 0`,
   `g₂ = repSrcTen w` (`OldRepIsRep`): the coefficient of `transOp T₂` is
   `coefOf R (transField .. g₂)`.
2. `RepairSepBridge` (proved, `PhaseGradient/L8`): a separated source `T` (period `2εc`, old disk
   `|z'| ≤ R√(5ν/6)`, finite `L²_τL²` moment, axisymmetric) with the same separated responses and
   `‖T‖_{L²_τL^{22/19}} ≤ F_r`; hence `transField .. g₂ = sepTrans .. T` (`sepTrans_congr`).
3. `TransVanishOff`: the transitions vanish off the annulus `0.8/ν ≤ s ≤ 1/ν` (5312-5316), so
   `LateVelGain` gives the late-output gain `e^{-4γ/(9ν)}` (5317-5318).
4. `TransSepChart`: `R⁻¹‖𝒩_v(transitions)‖_{Y_2} ≤ P_ν ε^{34/11}‖T‖_{L²_τL^{22/19}}`
   (5590-5592; the gap is `D = (1-√(5/6))R√ν`, so `R⁻¹D^{-23/11} ≍ ν^{-23/22}ε^{34/11}`).
5. `repairSource` (proved): `F_r ≤ P_νρR|N_ν|G(w)`; `RepMargin` (5601-5605, first conjunct, with
   `S^{23/22} ≥ 1`): the margin `23γ/99 ≥ 31γ/165`.

## The transition bound (`TransSepChart`, a composition)

`TransSepDom` (pointwise): `|sepTrans| ≤ P_ν · transMaj` with the majorant
`transMaj = 1_ann (sepDom₀ + L⁻¹ sepDom₁ + L⁻² outMaj)`, `L = R√ν`, from `TransVanishOff`,
`TransCutPoint` (the cutoff factor of `(𝒞_y - χ_y)W_μ`), `TransCommPoint` (the commutator
`[D_{μ+1}, 𝒞_y]X₀` in terms of `X₀`, `∇X₀`, `Ψ_{X₀}`, 4203-4214, 3700-3712), `SepX0Dom`
(`IIIa.SepWDominated` for `μ`, `μ+1`) and `OutPrimPointwise` (proved, `Sub/PartIII-b_C_rep_2_4`).
`TransMajChart`: the chart `L²` norm of the majorant, from `ChartPhysL2`
(`Sub/PartIII-b_C_rep_5_2_1Org`), `TransMajFacts`, `IIIa.SepDomYoung` (`sep:repair-energy`,
`p = 22/19`, `q = 2`, `b = 11/7`) and `OutMajAnnulusL2` (the energy version of the outward
primitive bound: `VertYoungL2`, `AnnulusFubiniL2`, with the proved `outMajReduce`,
`vprofHolder`, `vertMeasurable`).
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal
open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-! ## 1. The transition field of a separated source -/

/-- The commutator `[D_{μ+1}, 𝒞_y]X₀ = D_{μ+1}(𝒞_yX₀) - 𝒞_y(D_{μ+1}X₀)` of a separated source
`T` (source 4203-4214, 5312-5316). -/
def sepComm (ν μ R : ℝ) (χy : ℝ → ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ)
    (y : Space) : Space :=
  physDmu ν (μ + 1) (sepWX ν μ R χy T) τ y -
    wardStreamCut ν R χy (physDmu ν (μ + 1) (sepX0 ν μ T)) τ y

/-- Both stream transitions `(𝒞_y - χ_y)W_μ + [D_{μ+1}, 𝒞_y]X₀` of a separated source `T`
(source 5312-5316); `transField` is the case `T = oldPhys R c g` (`transField_eq_sepTrans`). -/
def sepTrans (ν μ R : ℝ) (χy : ℝ → ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ)
    (y : Space) : Space :=
  streamCorr ν R χy (sepWre ν μ T) τ y + sepComm ν μ R χy T τ y

theorem transField_eq_sepTrans (ν μ R c : ℝ) (χy : ℝ → ℝ) (g : Chart → Ten3) :
    transField ν μ R c χy g = sepTrans ν μ R χy (oldPhys R c g) := rfl

/-- The transitions only see the separated responses of the source. -/
theorem sepTrans_congr {ν μ R : ℝ} {χy : ℝ → ℝ} {T T' : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ}
    (h : ∀ (μ' : ℂ) (y : Space) (τ : ℝ), IIIa.sepW ν μ' T y τ = IIIa.sepW ν μ' T' y τ) :
    sepTrans ν μ R χy T = sepTrans ν μ R χy T' := by
  have h1 : sepWre ν μ T = sepWre ν μ T' := by
    funext τ y
    simp only [sepWre, h]
  have h2 : sepX0 ν μ T = sepX0 ν μ T' := sepX0_congr h
  funext τ y
  unfold sepTrans sepComm sepWX
  rw [h1, h2]

/-! ## 2. The majorant -/

/-- The transition length `L = R√ν` (inner radius of the annulus `streamAnn`, source 4164-4167). -/
def transLen (ν R : ℝ) : ℝ := R * Real.sqrt ν

/-- The radial gap `D = R√ν - R√(5ν/6)` between the young receiver and the old disk (4166-4167). -/
def transGap (ν R : ℝ) : ℝ := R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6)

/-- Order-zero component `1_ann sepDom₀` (`a = 0`, gap `D`). -/
def transMajW (ν R : ℝ) (g : ℝ → Space → ℝ≥0∞) (τ : ℝ) (y : Space) : ℝ≥0∞ :=
  (streamAnn ν R).indicator (fun y => IIIa.sepDom 0 0 (transGap ν R) g τ y) y

/-- Order-one component `1_ann L⁻¹ sepDom₁`. -/
def transMajD (ν R : ℝ) (g : ℝ → Space → ℝ≥0∞) (τ : ℝ) (y : Space) : ℝ≥0∞ :=
  (streamAnn ν R).indicator
    (fun y => ENNReal.ofReal (transLen ν R)⁻¹ * IIIa.sepDom 0 1 (transGap ν R) g τ y) y

/-- Stream-primitive component `1_ann L⁻² outMaj` (source 3684-3699, 4181-4192). -/
def transMajS (ν R : ℝ) (g : ℝ → Space → ℝ≥0∞) (τ : ℝ) (y : Space) : ℝ≥0∞ :=
  (streamAnn ν R).indicator
    (fun y => ENNReal.ofReal ((transLen ν R)⁻¹ ^ 2) * outMaj 0 (transGap ν R) g τ (ϱ y) (y 2)) y

/-- The transition majorant (source 3684-3712: the cutoff correction and commutators have the
separated-kernel majorants, with `D^{-1}` per derivative). -/
def transMaj (ν R : ℝ) (g : ℝ → Space → ℝ≥0∞) (τ : ℝ) (y : Space) : ℝ≥0∞ :=
  transMajW ν R g τ y + transMajD ν R g τ y + transMajS ν R g τ y

/-- Measurable, `P`-periodic in the phase, axisymmetric in `y` (the hypotheses of `ChartPhysL2`). -/
def ChartGood (P : ℝ) (G : ℝ → Space → ℝ≥0∞) : Prop :=
  Measurable (Function.uncurry G) ∧ (∀ τ y, G (τ + P) y = G τ y) ∧
    ∀ τ (y y' : Space), y' 2 = y 2 → y' 0 ^ 2 + y' 1 ^ 2 = y 0 ^ 2 + y 1 ^ 2 → G τ y' = G τ y

/-! ## 3. Leaves -/

/-- **Representatives of the old repair source** (source 5153-5157; `chiOStrApply`, `repPart`):
`χ_o(0, (M_Uw)₂)` has thin component `0` and repair component `repSrcTen w = (χ_oM_Uw)₂`, a.e. for
the gain measures. -/
def OldRepIsRep : Prop :=
  ∀ (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (w : LVel Pl L),
    IsRep Pl K L (oldRep Pl K L w) 0 (repSrcTen Pl K L w)

/-- **The transitions vanish off the annulus** (source 5312-5316: "They are supported on
`0.8/ν < s < 1/ν`"; 4164-4167): off the axis, where `ν·age < 4/5` the cutoff is `≡ 1` near `y`
(so `𝒞_y = id` there and both transitions vanish), and where `ν·age > 1` it is `≡ 0` near `y`. -/
def TransVanishOff : Prop :=
  ∀ (ν μ R : ℝ) (χy : ℝ → ℝ), IsStreamCutoff χy → 0 < ν → 0 < R →
    ∀ (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (τ : ℝ) (y : Space), 0 < ϱ y →
      (ν * age R y < 4 / 5 ∨ 1 < ν * age R y) → sepTrans ν μ R χy T τ y = 0

/-- **Late-output gain** (source 5317-5318): a body velocity whose coefficient vanishes at ages
`s < 0.8/ν` has gain norm at most `e^{-4γ/(9ν)}` times its ungained normalized norm
(`g(s)⁻¹ ≤ e^{-4γ/(9ν)}` for `s ≥ 0.8/ν`, `ftGain_late`). -/
def LateVelGain : Prop :=
  ∀ (c γ ν : ℝ), 0 ≤ γ → 0 < ν → ∀ (v : VelG c γ ν) (F : Chart → Merid),
    (v : Chart → Merid) =ᵐ[bodyMeasure c γ ν] F →
    (∀ p : Chart, 0 < p.1 → ν * p.1 < 4 / 5 → F p = 0) →
    ENNReal.ofReal ‖v‖ ≤
      ENNReal.ofReal (Real.exp (-(4 * γ / 9) / ν)) * eLpNorm F 2 (srcMeasure c)

/-- **The first transition, pointwise** (source 4180-4186, 3684-3692: `χ_y'/r = O(L⁻²)`):
`|(𝒞_y - χ_y)Z| = |χ̂_y'(ν·age)|·2ν·age/ϱ²·|Ψ_Z| ≤ C L⁻²|Ψ_Z|` on the annulus
(`ν·age ≤ 1`, `ϱ ≥ L`), and `0` off it (`χ̂_y' = 0` outside `[4/5, 1]`). -/
def TransCutPoint : Prop :=
  ∀ χy : ℝ → ℝ, IsStreamCutoff χy → ∃ C : ℝ, 0 ≤ C ∧ ∀ (ν R : ℝ), 0 < ν → 0 < R →
    ∀ (Z : ℝ → Space → Space) (τ : ℝ) (y : Space), 0 < ϱ y →
      ‖streamCorr ν R χy Z τ y‖ₑ ≤
        (streamAnn ν R).indicator (fun y => ENNReal.ofReal (C * (transLen ν R)⁻¹ ^ 2) *
          ENNReal.ofReal |outPrim Z τ (ϱ y) (y 2)|) y

/-- **Domination of `X₀` and `∇X₀`** (source 3604-3623, 4171: `X₀ = W_μ - W_{μ+1}`): at receivers
`|y'| ≥ r_i`, `|X₀| ≤ C sepDom₀` and `|∇X₀| ≤ C(sepDom₀ + sepDom₁)` (gap `r_i - r_o`, weight
`λ^0 ≥ λ^{2μ+2}, λ^{2μ+4}`), from `IIIa.SepWDominated` for `μ` and `μ+1`, `IIIa.SepKernelBounds`
and `SepWSmoothOn`. -/
def SepX0Dom : Prop :=
  ∀ σ₁ σ₂ : ℝ, -(1 / 4) < σ₁ → ∃ C : ℝ, 0 ≤ C ∧
    ∀ (ν μ rOut rIn P : ℝ), 0 < ν → μ ∈ Icc σ₁ σ₂ → 0 ≤ rOut → rOut < rIn → 0 < P →
      ∀ T, IIIa.IsSepSource P rOut T → SepMoment P T → ∀ (τ : ℝ) (y : Space), rIn ≤ ϱ y →
        ‖sepX0 ν μ T τ y‖ₑ ≤
            ENNReal.ofReal C * IIIa.sepDom 0 0 (rIn - rOut) (IIIa.srcNorm T) τ y ∧
          ‖fderiv ℝ (sepX0 ν μ T τ) y‖ₑ ≤
            ENNReal.ofReal C * (IIIa.sepDom 0 0 (rIn - rOut) (IIIa.srcNorm T) τ y +
              IIIa.sepDom 0 1 (rIn - rOut) (IIIa.srcNorm T) τ y)

/-- **The second transition, pointwise** (source 4203-4214, 3700-3712: `𝒬 = [B, 𝒞_χ] -
ν[Δ, 𝒞_χ]`; "derivatives of `χ` cost `D⁻¹`, `Bχ` is bounded, and each extra Laplacian costs
`νD⁻²`"; `Ψ_{AZ} = AΨ_Z + Ψ_Z`, `Ψ_{ΔZ} = (∂_r² - r⁻¹∂_r + ∂_z²)Ψ_Z`, `∂_rΨ_Z = rZ_z`): on the
annulus, `[D_{μ+1}, 𝒞_y]X₀` is a combination of `X₀`, `∇X₀` and `Ψ_{X₀}` with cutoff
coefficients `O(1)`, `O(L⁻¹)`, `O(L⁻²)` (`ν ≤ 1`, `νL⁻² = R⁻² ≤ 1`); the phase derivative and the
second derivatives of `X₀` cancel. -/
def TransCommPoint : Prop :=
  ∀ σ₁ σ₂ : ℝ, -(1 / 4) < σ₁ → ∀ χy : ℝ → ℝ, IsStreamCutoff χy → ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧
    ∀ (ν μ R P : ℝ), 0 < ν → ν ≤ 1 → 1 ≤ R → 0 < P → μ ∈ Icc σ₁ σ₂ →
      ∀ T, IIIa.IsSepSource P (R * Real.sqrt (5 * ν / 6)) T → SepMoment P T → IsAxiSource T →
        ∀ (τ : ℝ) (y : Space), y ∈ streamAnn ν R →
          ‖sepComm ν μ R χy T τ y‖ₑ ≤ ENNReal.ofReal (C * ν⁻¹ ^ k) *
            (‖sepX0 ν μ T τ y‖ₑ + ENNReal.ofReal (transLen ν R)⁻¹ * ‖fderiv ℝ (sepX0 ν μ T τ) y‖ₑ +
              ENNReal.ofReal ((transLen ν R)⁻¹ ^ 2) *
                ENNReal.ofReal |outPrim (sepX0 ν μ T) τ (ϱ y) (y 2)|)

/-- **Facts on the three majorant components** (source 2683, 3611-3617): for a separated
axisymmetric source, each component is jointly measurable, `P`-periodic and axisymmetric. -/
def TransMajFacts : Prop :=
  ∀ (ν R P : ℝ), 0 < ν → 0 < R → 0 < P →
    ∀ T, IIIa.IsSepSource P (R * Real.sqrt (5 * ν / 6)) T → IsAxiSource T →
      ChartGood P (transMajW ν R (IIIa.srcNorm T)) ∧ ChartGood P (transMajD ν R (IIIa.srcNorm T)) ∧
        ChartGood P (transMajS ν R (IIIa.srcNorm T))

/-- **Vertical Young in `L²`** (source 3631-3646 in one dimension, 4181-4192):
`‖(D²+t²)^{-1}‖_{L^{11/7}(ℝ)} = C D^{-2+7/11}`, Young `1 + 1/2 = 19/22 + 7/11`, dilation
`λ^{-1+19/22}`, Minkowski in `λ` (`∫_0^1 λ^{a-3/22} dλ ≤ 22/19` for `a ≥ 0`) and the
translation invariance of the normalized `L²_τ` norm of a `P`-periodic function. -/
def VertYoungL2 : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (a rIn D P : ℝ), 0 ≤ a → 0 < D → 0 < rIn → 0 < P →
    ∀ h : ℝ → ℝ → ℝ≥0∞, Measurable (Function.uncurry h) → (∀ τ s, h (τ + P) s = h τ s) →
      ltauLq1 P 2 (vertRedH a rIn D h) ≤
        ENNReal.ofReal (C * (rIn / D) * D ^ (-2 + 7 / 11 : ℝ)) * ltauLq1 P (22 / 19) h

/-- **Fubini on the transition annulus in `L²`** (source 4164-4167): the annulus
`R√ν ≤ ϱ ≤ R√(5ν/4)` has horizontal area `πνR²/4`. -/
def AnnulusFubiniL2 : Prop :=
  ∀ (ν R P : ℝ), 0 < ν → 0 < R → 0 < P → ∀ F : ℝ → ℝ → ℝ≥0∞, Measurable (Function.uncurry F) →
    IIIa.ltauLq P 2 (fun τ => (streamAnn ν R).indicator (fun y => F τ (y 2))) =
      ENNReal.ofReal ((Real.pi * ν * R ^ 2 / 4) ^ (1 / 2 : ℝ)) * ltauLq1 P 2 F

/-- **The outward primitive majorant in `L²_τL²`** (source 4181-4192, 3651-3656, 5590-5592):
`‖1_ann outMaj a D g‖_{L²_τL²} ≤ C (R√ν)^{-1/11}‖g‖_{L²_τL^{22/19}}` (`(R√ν)·D^{-15/11}·r_o^{3/11}`;
composition of `outMajReduce`, `vprofHolder`, `vertMeasurable`, `VertYoungL2`,
`AnnulusFubiniL2`). -/
def OutMajAnnulusL2 : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (ν R P a : ℝ), 0 < ν → 0 < R → 0 < P → 0 ≤ a →
    ∀ g : ℝ → Space → ℝ≥0∞, Measurable (Function.uncurry g) → (∀ τ z, g (τ + P) z = g τ z) →
      (∀ τ z, R * Real.sqrt (5 * ν / 6) < ϱ z → g τ z = 0) →
        IIIa.ltauLq P 2 (fun τ => (streamAnn ν R).indicator
            (fun y => outMaj a (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6)) g τ (ϱ y) (y 2))) ≤
          ENNReal.ofReal (C * (R * Real.sqrt ν) ^ (-(1 / 11 : ℝ))) * IIIa.ltauLq P (22 / 19) g

/-- **Pointwise domination of both transitions** (composition of `TransVanishOff`,
`TransCutPoint`, `TransCommPoint`, `SepX0Dom`, `OutPrimPointwise`). -/
def TransSepDom : Prop :=
  ∀ σ₁ σ₂ : ℝ, -(1 / 4) < σ₁ → ∀ χy : ℝ → ℝ, IsStreamCutoff χy → ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧
    ∀ (ν μ R P : ℝ), 0 < ν → ν ≤ 1 → 1 ≤ R → 0 < P → μ ∈ Icc σ₁ σ₂ →
      ∀ T, IIIa.IsSepSource P (R * Real.sqrt (5 * ν / 6)) T → SepMoment P T → IsAxiSource T →
        ∀ (τ : ℝ) (y : Space), 0 < ϱ y →
          ‖sepTrans ν μ R χy T τ y‖ₑ ≤
            ENNReal.ofReal (C * ν⁻¹ ^ k) * transMaj ν R (IIIa.srcNorm T) τ y

/-- **The chart `L²` norm of the majorant** (source 2683-2689, 3651-3656, 5590-5592): with
`R = ε⁻¹`, `R⁻¹L^{-23/11} = ν^{-23/22}ε^{34/11}` (composition of `ChartPhysL2`, `TransMajFacts`,
`IIIa.SepDomYoung`, `OutMajAnnulusL2`). -/
def TransMajChart : Prop :=
  ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ (ν ε c : ℝ), 0 < ν → ν ≤ 1 → 0 < ε → ε ≤ 1 → 0 < c →
    ∀ T, IIIa.IsSepSource (2 * ε * c) (ε⁻¹ * Real.sqrt (5 * ν / 6)) T → IsAxiSource T →
      (∫⁻ p, ENNReal.ofReal p.1⁻¹ *
          transMaj ν ε⁻¹ (IIIa.srcNorm T) (NearInst.chartTau ε⁻¹ p) (NearInst.chartY ε⁻¹ p) ^
            (2 : ℝ) ∂srcMeasure c) ^ (1 / 2 : ℝ) ≤
        ENNReal.ofReal (C * ν⁻¹ ^ k * ε ^ (34 / 11 : ℝ)) *
          IIIa.ltauLq (2 * ε * c) (22 / 19) (IIIa.srcNorm T)

/-- **Both transitions in the ungained normalized norm** (source 5590-5592, 3651-3656, 3684-3712;
composition of `TransSepDom` and `TransMajChart`):
`R⁻¹‖𝒩_v(transitions)‖_{Y_2} ≤ P_ν ε^{34/11}‖T‖_{L²_τL^{22/19}}`. -/
def TransSepChart : Prop :=
  ∀ σ₁ σ₂ : ℝ, -(1 / 4) < σ₁ → ∀ χy : ℝ → ℝ, IsStreamCutoff χy → ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧
    ∀ (ν μ ε c : ℝ), 0 < ν → ν ≤ 1 → 0 < ε → ε ≤ 1 → 0 < c → μ ∈ Icc σ₁ σ₂ →
      ∀ T, IIIa.IsSepSource (2 * ε * c) (ε⁻¹ * Real.sqrt (5 * ν / 6)) T →
        SepMoment (2 * ε * c) T → IsAxiSource T →
          eLpNorm (coefOf ε⁻¹ (sepTrans ν μ ε⁻¹ χy T)) 2 (srcMeasure c) ≤
            ENNReal.ofReal (C * ν⁻¹ ^ k * ε ^ (34 / 11 : ℝ)) *
              IIIa.ltauLq (2 * ε * c) (22 / 19) (IIIa.srcNorm T)

/-! ## 4. Assembly -/

theorem coefOf_eq_zero_of {R : ℝ} {F : ℝ → Space → Space} {p : Chart}
    (h : F (NearInst.chartTau R p) (NearInst.chartY R p) = 0) : coefOf R F p = 0 := by
  have hz : (!₂[(0 : ℝ), 0] : Merid) = 0 := by
    ext i; fin_cases i <;> rfl
  unfold coefOf
  rw [h]
  simp only [PiLp.zero_apply]
  rw [hz, smul_zero]

/-- **Both transitions at one level** (5310-5318, 5590-5592, 5601-5605). -/
theorem transVelRep_level (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)
    (hχ : IsStreamCutoff K.χy)
    (hW : IsWardTriple (wardOps Pl K L μ).1 (wardOps Pl K L μ).2.1 (wardOps Pl K L μ).2.2 L.ε μ
      K.hχo K.χy L.U L.pres)
    (hS1 : SepYoungRepAt Pl K L μ) (hS2 : ShiftedResolventRepAt Pl K L μ)
    (hI : OldRepIsRep) (hV : TransVanishOff) (hG : LateVelGain) (hB : RepairSepBridge)
    (hγ : 0 ≤ gRate Pl) (hmZ : 0 ≤ K.mZ) (hC0 : 0 < K.C0)
    {CT : ℝ} {kT : ℕ} (hCT : 0 ≤ CT)
    (hTb : ∀ T, IIIa.IsSepSource (2 * L.ε * cOf L.ν) (L.ε⁻¹ * Real.sqrt (5 * L.ν / 6)) T →
      SepMoment (2 * L.ε * cOf L.ν) T → IsAxiSource T →
      eLpNorm (coefOf L.ε⁻¹ (sepTrans L.ν μ L.ε⁻¹ K.χy T)) 2 (srcMeasure (cOf L.ν)) ≤
        ENNReal.ofReal (CT * L.ν⁻¹ ^ kT * L.ε ^ (34 / 11 : ℝ)) *
          IIIa.ltauLq (2 * L.ε * cOf L.ν) (22 / 19) (IIIa.srcNorm T))
    {Cr : ℝ} {kr : ℕ} (hR : RepairSourceAt Pl K L Cr kr)
    {ωb CM : ℝ} {kM : ℕ} (hM : RepMarginAt Pl K L ωb CM kM) (hS : 1 ≤ L.Scut K)
    (w : LVel Pl L) :
    ‖transOp Pl K L μ hχ (repPart (multOp Pl K L w))‖ ≤
      CT * |Cr| * |CM| * L.ν⁻¹ ^ (kT + kr + kM) *
        Real.exp (-(31 * gRate Pl / 165 - ωb - 3 * K.m0 / 2) / L.ν) * ‖w‖ := by
  have hν := L.ν_pos
  have hε := L.ε_pos
  have hc : 0 < cOf L.ν := cOf_pos hν
  have hR0 : 0 < L.ε⁻¹ := inv_pos.2 hε
  have hρb : 0 < L.ρb Pl K := by
    unfold ReturnLevel.ρb UnforcedLeray.Short.IIb.rhoB
    have h1 := (L.params Pl).ν_pos
    have h2 := (L.params Pl).ε_pos
    exact mul_pos (mul_pos (mul_pos hC0 (inv_pos.2 (pow_pos h1 _))) (Real.exp_pos _))
      (Real.rpow_pos_of_pos h2 _)
  obtain ⟨T, hTS, hTM, hTA, hTW, hTN⟩ := hB (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν L.ε K.χo
    K.hχo hc hρb hmZ hν hε (multOp Pl K L w)
  have hcoef := transOp_coef_rep Pl K L μ hχ hW hS1 hS2 w (hI Pl K L w)
  have hF : transField L.ν μ L.ε⁻¹ (cOf L.ν) K.χy ((0 : Chart → Ten3) + repSrcTen Pl K L w) =
      sepTrans L.ν μ L.ε⁻¹ K.χy T := by
    rw [zero_add, transField_eq_sepTrans]
    exact sepTrans_congr hTW
  rw [hF] at hcoef
  have hvan : ∀ p : Chart, 0 < p.1 → L.ν * p.1 < 4 / 5 →
      coefOf L.ε⁻¹ (sepTrans L.ν μ L.ε⁻¹ K.χy T) p = 0 := by
    intro p hp hlt
    have hy : 0 < ϱ (NearInst.chartY L.ε⁻¹ p) := by
      rw [ϱ_chartY hR0 hp]; positivity
    refine coefOf_eq_zero_of ?_
    exact hV L.ν μ L.ε⁻¹ K.χy hχ hν hR0 T _ _ hy (Or.inl (by rw [age_chartY hR0 hp]; exact hlt))
  have g1 := hG (cOf L.ν) (gRate Pl) L.ν hγ hν _ _ hcoef hvan
  have g2 := hTb T hTS hTM hTA
  have hw : 0 ≤ ‖w‖ := norm_nonneg w
  have hρ : 0 ≤ rhoRep K L := by unfold rhoRep; positivity
  have hN : 0 ≤ gaugeN Pl L := norm_nonneg _
  have hpow : ∀ j : ℕ, 0 ≤ L.ν⁻¹ ^ j := fun j => by positivity
  have g3 : IIIa.ltauLq (2 * L.ε * cOf L.ν) (22 / 19) (IIIa.srcNorm T) ≤
      ENNReal.ofReal (|Cr| * L.ν⁻¹ ^ kr * rhoRep K L * L.ε⁻¹ * gaugeN Pl L * ‖w‖) := by
    refine hTN.trans ((hR w).trans (ENNReal.ofReal_le_ofReal ?_))
    have h0 : 0 ≤ L.ν⁻¹ ^ kr * rhoRep K L * L.ε⁻¹ * gaugeN Pl L * ‖w‖ := by positivity
    have h := mul_le_mul_of_nonneg_right (le_abs_self Cr) h0
    calc Cr * L.ν⁻¹ ^ kr * rhoRep K L * L.ε⁻¹ * gaugeN Pl L * ‖w‖
        = Cr * (L.ν⁻¹ ^ kr * rhoRep K L * L.ε⁻¹ * gaugeN Pl L * ‖w‖) := by ring
      _ ≤ |Cr| * (L.ν⁻¹ ^ kr * rhoRep K L * L.ε⁻¹ * gaugeN Pl L * ‖w‖) := h
      _ = _ := by ring
  set E := Real.exp (-(31 * gRate Pl / 165 - ωb - 3 * K.m0 / 2) / L.ν) with hEdef
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hS1' : 1 ≤ L.Scut K ^ (23 / 22 : ℝ) := Real.one_le_rpow hS (by norm_num)
  have hm : L.ε ^ (34 / 11 : ℝ) * rhoRep K L * L.ε⁻¹ * Real.exp (-(4 * gRate Pl / 9) / L.ν) *
      gaugeN Pl L ≤ |CM| * L.ν⁻¹ ^ kM * E := by
    have hb : 0 ≤ L.ε ^ (34 / 11 : ℝ) * rhoRep K L * L.ε⁻¹ *
        Real.exp (-(4 * gRate Pl / 9) / L.ν) * gaugeN Pl L := by positivity
    calc L.ε ^ (34 / 11 : ℝ) * rhoRep K L * L.ε⁻¹ * Real.exp (-(4 * gRate Pl / 9) / L.ν) *
          gaugeN Pl L
        ≤ (L.ε ^ (34 / 11 : ℝ) * rhoRep K L * L.ε⁻¹ * Real.exp (-(4 * gRate Pl / 9) / L.ν) *
            gaugeN Pl L) * L.Scut K ^ (23 / 22 : ℝ) := le_mul_of_one_le_right hb hS1'
      _ = L.ε ^ (34 / 11 : ℝ) * L.Scut K ^ (23 / 22 : ℝ) * rhoRep K L * L.ε⁻¹ *
            Real.exp (-(4 * gRate Pl / 9) / L.ν) * gaugeN Pl L := by ring
      _ ≤ CM * L.ν⁻¹ ^ kM * E := hM.1
      _ ≤ |CM| * L.ν⁻¹ ^ kM * E :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) (hpow _)) hE0
  have hCa : 0 ≤ CT * L.ν⁻¹ ^ kT * L.ε ^ (34 / 11 : ℝ) :=
    mul_nonneg (mul_nonneg hCT (hpow _)) (Real.rpow_nonneg hε.le _)
  have hX0 : 0 ≤ CT * |Cr| * |CM| * L.ν⁻¹ ^ (kT + kr + kM) * E * ‖w‖ :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCT (abs_nonneg _))
      (abs_nonneg _)) (hpow _)) hE0) hw
  refine ennChain3 g1 g2 g3 (Real.exp_pos _).le hCa ?_ hX0
  have hQ : 0 ≤ CT * |Cr| * L.ν⁻¹ ^ kT * L.ν⁻¹ ^ kr * ‖w‖ :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCT (abs_nonneg _)) (hpow _)) (hpow _)) hw
  calc Real.exp (-(4 * gRate Pl / 9) / L.ν) * (CT * L.ν⁻¹ ^ kT * L.ε ^ (34 / 11 : ℝ) *
        (|Cr| * L.ν⁻¹ ^ kr * rhoRep K L * L.ε⁻¹ * gaugeN Pl L * ‖w‖))
      = (CT * |Cr| * L.ν⁻¹ ^ kT * L.ν⁻¹ ^ kr * ‖w‖) * (L.ε ^ (34 / 11 : ℝ) * rhoRep K L *
          L.ε⁻¹ * Real.exp (-(4 * gRate Pl / 9) / L.ν) * gaugeN Pl L) := by ring
    _ ≤ (CT * |Cr| * L.ν⁻¹ ^ kT * L.ν⁻¹ ^ kr * ‖w‖) * (|CM| * L.ν⁻¹ ^ kM * E) :=
        mul_le_mul_of_nonneg_left hm hQ
    _ = CT * |Cr| * |CM| * L.ν⁻¹ ^ (kT + kr + kM) * E * ‖w‖ := by rw [pow_add, pow_add]; ring

/-- **The stream-transition leaf `AgeVelTransRep`** (source 5310-5318, 5590-5592, 5601-5605,
5687-5689) from the leaves of §3, the transition coefficient facts of `YRepStream/Trans.lean`
(`SepYoungRep`, `ShiftedResolventRep`) and the margins `RepMargin`, with `k₀ = 2`. -/
theorem ageVelTransRep_of (Pl : PlanarData) (σ₀ mZ dm dp : ℝ)
    (h1 : SepYoungRep dm dp) (h2 : ShiftedResolventRep dm dp) (hI : OldRepIsRep)
    (hV : TransVanishOff) (hG : LateVelGain) (hT : TransSepChart)
    (hM : RepMargin Pl σ₀ mZ dm dp) : AgeVelTransRep Pl σ₀ mZ dm dp := by
  refine ⟨2, fun D hPl hσ hmZ hst => ?_⟩
  have hσ' : -(1 / 4 : ℝ) < D.σ₀ / 2 := by linarith [hst.sigma_pos]
  obtain ⟨CT, kT, hCT, hTb⟩ := hT (D.σ₀ / 2) ((D.σ₀ + 1 / 4) / 2) hσ' D.K.χy hst.chiY
  obtain ⟨Cr, kr, hR⟩ := repairSource D hst
  obtain ⟨CM, kM, hMn⟩ := hM D hPl hσ hmZ hst
  refine ⟨CT * |Cr| * |CM|, kT + kr + kM, ?_⟩
  have hev1 := mu_eventually_mem D hst.omega_ne hst.sigma_pos hst.sigma_lt
  have hev2 := retNu_retEps_eventually_le_one hst.omega_ne hst.gamma_pos D.coeff_ne
  filter_upwards [hev1, hev2, h1 D hst, h2 D hst, hst.pins, hR, hMn] with
    n e1 e2 s1 s2 pins hRn hMn' z hz w
  have hW : IsWardTriple (wardOps D.Pl D.K (D.level n) (D.mu n z)).1
      (wardOps D.Pl D.K (D.level n) (D.mu n z)).2.1 (wardOps D.Pl D.K (D.level n) (D.mu n z)).2.2
      (D.level n).ε (D.mu n z) D.K.hχo D.K.χy (D.level n).U (D.level n).pres :=
    Classical.epsilon_spec (pins z hz).ward
  have hν := (D.level n).ν_pos
  have hε := (D.level n).ε_pos
  have hS : 1 ≤ (D.level n).Scut D.K :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hε e2.2 (by linarith [hst.b_pos])
  exact transVelRep_level D.Pl D.K (D.level n) (D.mu n z) hst.chiY hW (s1 z hz) (s2 z hz) hI hV
    hG repairSepBridge hst.gamma_pos.le (by linarith [hst.mZ_gt]) hst.C0_pos hCT
    (hTb _ _ _ _ hν e2.1 hε e2.2 (cOf_pos hν) (e1 z hz)) hRn hMn' hS w

end UnforcedLeray.Short.PartIIIb.Concrete
