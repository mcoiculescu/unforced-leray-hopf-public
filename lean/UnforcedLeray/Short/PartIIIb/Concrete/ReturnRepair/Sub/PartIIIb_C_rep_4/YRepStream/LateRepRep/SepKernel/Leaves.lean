import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.LateRepRep.SepKernel.Props
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_1Org
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.Defs

/-!
# `PartIII-b:C/rep/4/4/1/org/6/1/org` (c): the leaves of the far kernel `FarRepRepUng`

Source `the November 2 reference manuscript` 5303-5306 (far mask `s < S`,
`t > e^δs`, `S = ε^{-b}`), 3902-3920 and 3611-3621 (`S_far = 1_{s<S,t>e^δs}S_μ` in the exact
kernel realization `sep:resolvent`), 3604-3610 (`sep:kernel`: `|∇K_t(x)| ≤ C|x|^{-4}`), 3624-3646
(`sep:young`: `‖1_{≥D}|x|^{-4-j}‖_{L^b} = CD^{-4-j+3/b}`, Young with dilation, Minkowski in `λ`),
5323-5339 ("the general separated kernel bounds ... the repair-to-repair entry uses the source
`L^{22/19}` norm and the `L^{11/3}` kernel"; receiver factor `√ρ`, 5336), 5134-5139
(`‖r_b‖_{C_τL^{11/4}} ≤ P_νρ`, `ρ = ε^{3/11}e^{m₀/ν}`), 2683-2700 (lifts `𝒩_v b = √s b`,
`𝒩_T T = sT`, `R⁻¹‖𝒩_v b‖_{Y_2} = √π‖b‖_H`, the norm of `ρ_b^{-1/2}H_T`).

The source's three facts for the repair-to-repair entry, in physical terms, at `R = ε⁻¹`,
`P = 2εc`:

* **(a) the separated kernel** (`FarVelPointwise`, `FarVelYoungBox`): on a box source `f` the far
  velocity `𝒩_v farOut f` (the exact kernel realization of `S_far`, `IsFarMaskG`) satisfies
  `‖𝒩_v farOut f‖_{L²_τL^{22/3}} ≤ C D₀^{-35/11}‖𝒩_Tf‖_{L²_τL^{22/19}}`,
  `D₀ = (1-e^{-δ/2})R/√S`, i.e. `C(1-e^{-δ/2})^{-35/11}ε^{35/11}S^{35/22}`.  Route: the pointwise
  majorant of `farOut` by the dilated positive kernel `dilMaj` with gap `D₀` (proved pieces:
  `farPointwiseMajorant_of`, `farMajorantPointwise_of`, `dilMajAxisym_of`, `gAxFacts_holds`),
  then `sep:young` for the scalar dilation integral with `j = 0`, `p = 22/19`, `q = 22/3`,
  `b = 11/3` (`IIIa.sepDomYoung`, proved; `dilMaj μ d = IIIa.sepDom (2μ+2) 0 d`).
* **(b) the lift identity** (`SopSubIsFarSeq`, task `PartIII-b:C/rep/5/1/1/1`, and
  `FarRepExtend`): at standing levels `Sop - SNop` is the far mask `Sf` with `IsFarMaskG ε⁻¹ μ δ S`,
  i.e. on box repair sources its output is a.e. `farOut f`; the bound extends from box sources
  to every repair source by truncation (`|1_{A_n}T₂| ≤ |T₂|`, so the source norm does not grow),
  continuity of `M_US_far` and Fatou.
* **(c) the receiver conversion** (`RepRecvConv`): `(M_Uv)₂ = r_b⊗v + v⊗r_b`, the normalized
  lift `‖T₂‖_{H_T} = (πR²)^{-1/2}‖𝒩_TT₂‖_{L²_τL²}` and Hölder `1/2 = 4/11 + 3/22` with
  `‖r_b(τ)‖_{L^{11/4}} ≤ ρ_b`:
  `‖(M_Uv)₂‖_{ρ_b^{-1/2}H_T} ≤ 2π^{-1/2}R⁻¹ρ_b^{1/2}‖𝒩_vv‖_{L²_τL^{22/3}} ≤ P_νε^{25/22}e^{m₀/(2ν)}‖𝒩_vv‖_{L²_τL^{22/3}}`.

Exponents (`Assembly.lean`): `ε^{25/22}·ε^{35/11} = ε^{95/22}`, `S^{35/22} = ε^{-35b/22} ≤ ε^{-2b}`
(`k₀ = 2`).

**Note on the receiver exponent.**  The receiver `(M_Uv)₂` contains the velocity `v`, not its
gradient, so the `L^{11/3}` kernel of 5338-5339 is the order-four velocity kernel (`D^{-35/11}`);
the power `ε^{46/11} = ε·ε^{35/11}` of the phase-gradient estimate 5214-5217 (order-five gradient
kernel in `L^{11/3}`) coincides with `R⁻¹` times it, which is why the table entry carries
`ε^{46/11}·√ρ = ε^{95/22}e^{m₀/(2ν)}` before `repair:source`.
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open UnforcedLeray.Blueprint.Planar (PlanarData)
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **(a1) Pointwise majorant of the lifted far velocity** (source 3611-3621, 3604-3610,
3996-3998, 5303-5306): there is an absolute `C` such that for `ε, c, ν, δ, S > 0`, every `μ`, every
box tensor `f` and every phase `τ`, for a.e. `y ∈ ℝ³`,
`|𝒩_v(farOut f)(τ,y)| ≤ C ∫_0^1 λ^{2μ+2} ∫ 1_{|y-λz| ≥ D₀}|y-λz|^{-4} s(z)|nsSym f|(τ+2logλ,z) dz dλ`
with the fixed gap `D₀ = (1-e^{-δ/2})R/√S`, `R = ε⁻¹` (`dilMaj`, `gAx`).  At the chart point `x`
of `(y,τ)`: `|𝒩_v b| = √s|b(x)|`, `|farOut f(x)| ≤ Cs^{-1/2}farMajE(x)` (`FarPointwiseMajorant`,
from `sep:kernel`), `farMajE(x) ≤ dilMaj(chartTau x)(chartY x)` for `0 < s < S`
(`FarMajorantPointwise`), and `dilMaj` of the axisymmetric `2c/R`-periodic profile `gAx` is
axisymmetric in `y` and `2c/R`-periodic in `τ` (`DilMajAxisym`, `GAxFacts`), while
`chartY x = (|y'|,0,y₃)` and `chartTau x ≡ τ` mod `2c/R`. -/
def FarVelPointwise : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (ε c ν δ S μ : ℝ), 0 < ε → 0 < c → 0 < ν → 0 < δ → 0 < S →
    ∀ f : Chart → Ten3, NearInst.IsBoxTensor f → ∀ τ : ℝ, ∀ᵐ y : Space,
      ‖velPhys ε⁻¹ c (NearInst.Masked.farOut ε⁻¹ c ν μ δ S f) (τ, y)‖ₑ ≤
        ENNReal.ofReal C *
          NearInst.Masked.dilMaj μ ((1 - Real.exp (-δ / 2)) * ε⁻¹ / Real.sqrt S)
            (NearInst.Masked.gAx ε⁻¹ c f) τ y

/-- **(a2) The separated kernel `L^{22/19} → L^{22/3}` on the far mask** (source 5323-5339 "the
repair-to-repair entry uses the source `L^{22/19}` norm and the `L^{11/3}` kernel", `sep:young`
3624-3646 with `j = 0`, `p = 22/19`, `q = 22/3`, `b = 11/3`: `-4 + 3/b = -35/11`; far mask
5303-5306): there is an absolute `C` such that for `ε, c, ν, δ, S > 0`, `μ > -1/4`, every box
tensor `f` and every measurable `b` a.e. equal to the far output `farOut f` (the exact kernel
realization of `S_far`, `IsFarMaskG`),
`‖𝒩_vb‖_{L²_τL^{22/3}} ≤ C(1-e^{-δ/2})^{-35/11}ε^{35/11}S^{35/22}‖𝒩_Tf‖_{L²_τL^{22/19}}`
(`= C D₀^{-35/11}‖·‖`, `D₀ = (1-e^{-δ/2})ε⁻¹S^{-1/2}`), period `P = 2εc`.  From `FarVelPointwise`,
`dilMaj μ d = IIIa.sepDom (2μ+2) 0 d`, `IIIa.sepDomYoung` (proved), `srcNorm (cartLift f) = gAx`
off the null axis (`CartLiftNormOffAxis`, `AxisNull`), and `wda_velPhys_congr`. -/
def FarVelYoungBox : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (ε c ν δ S μ : ℝ), 0 < ε → 0 < c → 0 < ν → 0 < δ → 0 < S →
    -(1 / 4) < μ → ∀ f : Chart → Ten3, NearInst.IsBoxTensor f →
      ∀ b : Chart → Merid, Measurable b →
        b =ᵐ[ageμ c (-3 / 2)] NearInst.Masked.farOut ε⁻¹ c ν μ δ S f →
        UnforcedLeray.Short.IIIa.ltauLq (2 * ε * c) (22 / 3)
            (fun τ y => ‖velPhys ε⁻¹ c b (τ, y)‖ₑ) ≤
          ENNReal.ofReal (C * (1 - Real.exp (-δ / 2)) ^ (-(35 / 11 : ℝ)) *
              ε ^ (35 / 11 : ℝ) * S ^ (35 / 22 : ℝ)) *
            phaseL2Lr (2 * ε * c) (22 / 19) (strPhys ε⁻¹ c f)

/-- **(c) The receiver conversion** (source 5336 "followed by `√ρ`", 5134-5139, 2683-2700, 4147):
for every standing sequence there are `C ≥ 0`, `k` with, for large `n` and every velocity `v`,
`‖(M_Uv)₂‖_{ρ_b^{-1/2}H_T} ≤ Cν^{-k}ε^{25/22}e^{m₀/(2ν)}‖𝒩_vv‖_{L²_τL^{22/3}}` (receiver without the
gain, `htUng`; period `2εc`).  Proof: the exact multiplier (`concreteBase_isExactMultiplier`,
`NearInst.multPinOfLink`): `𝒩_T(M_Uv)₂ = r_b⊗𝒩_vv + 𝒩_vv⊗r_b` (`cartLiftSymOuter_proved`,
`tensorNorm_symProd_le'`); the lift `P⁻¹∫₀ᴾ∫|𝒩_Tg|² = πR²‖g‖²_{H_T}` for the symmetric no-swirl
`g` (chart change of `FarMajorantL2/ChartChange`, `PolarReduction`, `AgeShift`); Hölder at each
phase `∫|r_b|²|V|² ≤ ‖r_b‖²_{11/4}‖V‖²_{22/3}` (`8/11 + 3/11 = 1`) with
`‖r_b(τ)‖_{L^{11/4}} ≤ ρ_b` (`IIb.ExactSplitII.energy`, `rbFacts`); so the bound holds with
`2π^{-1/2}ε√ρ_b`, and `√ρ_b = √C₀ ν^{-k₀/2}ε^{3/22}e^{m₀/(2ν)}` (`rhoB_eq`, `ν ≤ 1`). -/
def RepRecvConv (dm dp : ℝ) : Prop :=
  ∀ D : SeqData, D.RepairStanding dm dp → ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧
    ∀ᶠ n : ℕ in atTop, ∀ v : LVel D.Pl (D.level n),
      htUng (cOf (D.level n).ν) ((D.level n).ρb D.Pl D.K)
          ((multOp D.Pl D.K (D.level n) v).snd : Chart → Ten3) ≤
        ENNReal.ofReal (C * (D.level n).ν⁻¹ ^ k * (D.level n).ε ^ (25 / 22 : ℝ) *
            Real.exp (D.K.m0 / 2 / (D.level n).ν)) *
          UnforcedLeray.Short.IIIa.ltauLq (2 * (D.level n).ε * cOf (D.level n).ν) (22 / 3)
            (fun τ y => ‖velPhys (D.level n).ε⁻¹ (cOf (D.level n).ν) v (τ, y)‖ₑ)

/-- **(b2) Extension from box repair sources** (source 3905-3912: "we begin with smooth tensors
and then complete in the norms", the kernel pin is on the dense box class; 5323-5339): at one
level with `C₀ > 0`, for every bounded operator `Sf : Str → Vel` and every `A ∈ [0,∞]`, if the
bound `‖(M_USf(0,T₂))₂‖_{ρ_b^{-1/2}H_T} ≤ A‖𝒩_Tf‖_{L²_τL^{22/19}}` holds for every repair source
whose component sum is a.e. a box tensor `f`, it holds for every repair source with the norm of
`𝒩_TT₂`.  Proof: the truncations `T₂·1_{A_n}`, `A_n = {1/(n+1) ≤ s ≤ n, |η| ≤ n, |T₂| ≤ n}`
(as in `NearInst.Masked.boxDenseZ`) are box tensors, converge to `T₂` in `ρ_b^{-1/2}H_T`, and
`|𝒩_T(T₂1_{A_n})| ≤ |𝒩_TT₂|` pointwise (`cartLift_smul_pt`); `M_USf` is continuous, a subsequence
of `(M_USf(0,T₂1_{A_n}))₂` converges a.e. (`NearInst.ae_gainHTMeasure`), and Fatou bounds the
ungained norm of the limit. -/
def FarRepExtend : Prop :=
  ∀ (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel), 0 < K.C0 →
    ∀ (Sf : LStr Pl K L →L[ℝ] LVel Pl L) (A : ℝ≥0∞),
      (∀ (T : LStr Pl K L) (f : Chart → Ten3), NearInst.IsBoxTensor f →
        strSum (repPart T) =ᵐ[ageμ (cOf L.ν) (-1 / 2)] f →
        htUng (cOf L.ν) (L.ρb Pl K) ((multOp Pl K L (Sf (repPart T))).snd : Chart → Ten3) ≤
          A * phaseL2Lr (2 * L.ε * cOf L.ν) (22 / 19) (strPhys L.ε⁻¹ (cOf L.ν) f)) →
      ∀ T : LStr Pl K L,
        htUng (cOf L.ν) (L.ρb Pl K) ((multOp Pl K L (Sf (repPart T))).snd : Chart → Ten3) ≤
          A * phaseL2Lr (2 * L.ε * cOf L.ν) (22 / 19)
            (strPhys L.ε⁻¹ (cOf L.ν) ((repPart T).snd : Chart → Ten3))

end UnforcedLeray.Short.PartIIIb.Concrete
