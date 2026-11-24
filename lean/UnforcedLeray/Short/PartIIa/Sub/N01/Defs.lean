import UnforcedLeray.Short.PartIIa.StatementsNear
import UnforcedLeray.Short.PartIIa.StatementsFree
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Defs
import UnforcedLeray.Units.B0421.Phase

/-!
# `PartII-a:N01` (design): the stress maps `S_ε`, `S_0` of `near:free-energy`

Source of record: `the November 2 reference manuscript`,
lines 1638-1690 (`near/free-comparison.tex`: chart 1639-1643, measures 1644-1646, natural lifts
1647-1648, `div_ε` 1655-1666, `P_ε` 1669, `T_ε`, `S_ε` 1671-1674, completion 1675,
`near:free-energy` 1675-1683, the flat equation 1684-1689), with the Cartesian foundation 1339-1372
(`bg:common-body-graph`, the semigroup inverse), 1546-1567 (`free:weak-stress`,
`free:stress-energy`) and 1625-1632 (the transported stress map `J_v⁻¹ S_μ J_T`).

## Route (the source's: "the free Cartesian energy estimate, and its flat age-energy counterpart")

`ε > 0`.  For a smooth tensor test `m` (real), the accepted chart conjugation
`Masked.Realization.chartConjSmooth` (PartIII-b, source 1639-1675, 3893-3906) gives
`J_ε T_ε(s div_ε m) = (2π)^{-1/2} (μ - A)⁻¹ P_3D div 𝒩_T m` in the outer Cartesian space
`X ℂ³ P = L²(ℝ³ × ℝ/Pℤ)` of B0223 (`J_ε = B0223.liftVec`, `𝒩_T m = sm`).  The unitary
*phase lift* `U : X ℂ³ P → Y₂` (`IsPhaseLift`: `(UF)(τ)(y) = √P ε^{3/2} F(εy, τ)`, the change
of variables `y = x/ε = Rx` and the normalised phase measure, 1339-1343, 1639-1643) carries the
outer semigroup to the free semigroup `𝒯(t)` of `Y₂` (`PhaseSemigroupConj`, 1363-1372), the
physical Leray projection `B0226.P3D` to `lerayY` (`PhaseLerayConj`), and the outer divergence of
`𝒩_T m` to `√(Pε)` times the phase divergence of its rows (`PhaseDivScale`).  So
`U J_ε T_ε(s div_ε m) = (2π)^{-1/2}√(Pε) S_μ(𝒩_T m)` with `S_μ` the weak stress inverse of
`free:weak-stress` (`PartII-a:F14`), whence `free:stress-energy` and the norm of the tensor lift
(`CartLiftNorm`, 1644-1648: "both multiply norms by `√π R`") give `‖T_ε(s div_ε m)‖_H ≤
‖m‖_{H_T}/√(2(Re μ + 1/4)ν)`.  Complex tests split into two real ones (`TensorTestReIm`), and
completion from smooth tensors (`StressCompletion`, 1675) gives the bounded `S_ε`.

`ε = 0`.  `FlatSmoothBound` is the flat age-energy estimate on smooth tests (1684-1689: pairing
the flat equation `(∂_s + μ/s - νΔ)b = P_0 div_0 M` with `s^{-1/2} b̄`); completion as above.

## Note on the tensor norm

`HTSpace c` carries the Euclidean norm of the four components `(T_rr, T_rz, T_zz, T_φφ)`
(`StatementsNear.TensorVal`), while the Cartesian (Frobenius) norm of the lifted tensor counts
`T_rz` twice.  So the normalised tensor lift is not unitary for the Lean norm:
`‖J_T M‖² = ‖M‖² + ‖M_rz‖² ≤ 2‖M‖²` (`CartLiftNorm` states the `√2` form).  This changes only
constants.

## Leaf Props (tasks `PartII-a:N01/1` … `/8` here, `/9` … `/11` in `Sub/N01/FlatReduction.lean`;
`/12` records the dissipation part)

`PhaseLiftExists`, `PhaseSemigroupConj`, `PhaseLerayConj`, `PhaseDivScale`, `CartLiftRows`,
`CartLiftNorm`, `TensorTestReIm`, `StressCompletion`; `DissipationBound`.  `FlatSmoothBound` is the
intermediate flat statement, proved in `Sub/N01/FlatReduction.lean` from `FlatColumnC`,
`FlatVelTransport`, `FlatBlkTransport` (tasks `/9`-`/11`).  The assembly is `Sub/N01/Reduction.lean`
and `Sub/N01/Assembly.lean`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa.N01

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp
open UnforcedLeray.B0220 (Profile HSpace measureH)
open UnforcedLeray.B0223 (MeridC SpaceC)
open UnforcedLeray.Short.PartIIIb.Concrete (Chart Ten3)
open UnforcedLeray.Short.PartIIIb.NearInst (tv4 cartLift)
open UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization (IsCartTest cartDiv outerField toX)

/-! ## Concrete objects -/

/-- The rows of a real Cartesian tensor field `T(τ, z)` of the similarity variables, complexified:
row `i` at `(τ, z)` is `(T_{i0}, T_{i1}, T_{i2})(τ, z) ∈ ℂ³` (the tensor `𝒩_T m = sm` of 1647 as
an element of `Y₂(Sym₃)`, `StatementsFree.smoothTensor`). -/
def cartRowsC (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) : Fin 3 → ℝ × Space → CVec3 :=
  fun i x => WithLp.toLp 2 fun j => ((T x.1 x.2 i j : ℝ) : ℂ)

/-- **The phase lift** `U : X ℂ³ P → Y₂` (lines 1339-1343, 1639-1643): the outer Cartesian
variable `x` of B0223 is `x = εy` (`y = Rx`, `R = ε⁻¹`, the similarity variable of
`bg:common-body-graph`), and `Y₂` carries the normalised phase measure, so
`(UF)(τ)(y) = √P ε^{3/2} F(εy, τ)` for a.e. phase `τ` and a.e. `y`.  This formula determines
`U` (a.e. classes). -/
def IsPhaseLift (ε P : ℝ) [Fact (0 < P)] (U : B0223.X SpaceC P →ₗᵢ[ℂ] Yq P 2) : Prop :=
  ∀ F : B0223.X SpaceC P, ∀ᵐ τ ∂(AddCircle.haarAddCircle (T := P)),
    ((U F τ : Lp CVec3 2 (volume : Measure Space)) : Space → CVec3) =ᵐ[volume]
      fun y => (((Real.sqrt P * ε ^ (3 / 2 : ℝ) : ℝ) : ℂ)) •
        (F : B0223.PSpace P → SpaceC) (ε • y, τ)

/-! ## Leaf Props -/

/-- **`PartII-a:N01/1` — the phase lift exists** (lines 1339-1343, 1639-1643): for `ε > 0` there is
a complex linear isometry `U : X ℂ³ P → Y₂` with `(UF)(τ)(y) = √P ε^{3/2} F(εy, τ)`.
(Composite of the normalised dilation `B0223.dilN ε`, the swap `Space × ℝ/Pℤ → ℝ/Pℤ × Space`,
the normalisation `volume = P • haarAddCircle` on the circle, and the Fubini isometry
`FreeStress.prodLpEquiv`.) -/
def PhaseLiftExists : Prop :=
  ∀ (ε P : ℝ) [Fact (0 < P)], 0 < ε →
    ∃ U : B0223.X SpaceC P →ₗᵢ[ℂ] Yq P 2, IsPhaseLift ε P U

/-- **`PartII-a:N01/2` — the phase lift conjugates the outer semigroup to the free semigroup**
(lines 1363-1372: `S(t)h(y) = e^{t/2}[e^{ν(eᵗ-1)Δ}h](e^{t/2}y)` applied after the phase
translation; B0223 `S_formula`: the outer semigroup is the same formula with `νε²Δₓ` in
`x = εy`): `U ∘ S_ε(t) = 𝒯(t) ∘ U` for `t ≥ 0`. -/
def PhaseSemigroupConj : Prop :=
  ∀ (ν ε P : ℝ) [Fact (0 < P)] (hν : 0 < ν), 0 < ε →
    ∀ U : B0223.X SpaceC P →ₗᵢ[ℂ] Yq P 2, IsPhaseLift ε P U →
      ∀ t : ℝ, 0 ≤ t → ∀ F : B0223.X SpaceC P,
        U ((B0223.outerS (E := SpaceC) (P := P) hν ε).T t F) =
          B0421.phaseT (P := P) (q := 2) ENNReal.ofNat_ne_top ν t (U F)

/-- **`PartII-a:N01/3` — the phase lift conjugates the physical Leray projection to the phase
Leray projection** (line 1669: `P_ε` is the conjugated Cartesian Leray projection;
`B0226.P3D` is the orthogonal projection of `L²(dx dτ)` onto the fields with `div_x = 0`,
`B0414.lerayY_two` the orthogonal projection of `Y₂` onto the fields with solenoidal slices;
the dilation `x = εy` and the period identification preserve both classes). -/
def PhaseLerayConj : Prop :=
  ∀ (ε c P : ℝ) [Fact (0 < P)], 0 < ε → 0 < c → ∀ (hP : P = 2 * ε * c),
    ∀ U : B0223.X SpaceC P →ₗᵢ[ℂ] Yq P 2, IsPhaseLift ε P U →
      ∀ V : B0220.PhysL2 ε c,
        U (toX hP (B0226.P3D ε c V)) =
          lerayY P 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top (U (toX hP V))

/-- **`PartII-a:N01/4` — the outer divergence in phase variables** (lines 1639-1643,
1655-1665): for a smooth Cartesian tensor `T(τ, z)` the outer field is `T(τ, x/ε)`, so
`div_x = ε⁻¹ div_z`, and `U` multiplies by `√P ε^{3/2}`: the phase lift of the outer divergence is
`√(Pε)` times the phase divergence of the rows of `T`. -/
def PhaseDivScale : Prop :=
  ∀ (ε c P : ℝ) [Fact (0 < P)], 0 < ε → 0 < c → ∀ (hP : P = 2 * ε * c),
    ∀ U : B0223.X SpaceC P →ₗᵢ[ℂ] Yq P 2, IsPhaseLift ε P U →
      ∀ T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ, IsCartTest P T →
        ∀ hM : MemLp (cartDiv (outerField ε⁻¹ T)) 2 (B0220.physMeasure ε c),
          U (toX hP (hM.toLp _)) =
            ((Real.sqrt (P * ε) : ℝ) : ℂ) • testElem P 2 (tensorDiv (cartRowsC T))

/-- **`PartII-a:N01/5` — the rows of the tensor lift are a smooth symmetric phase tensor**
(lines 1647-1650: `𝒩_T m = sm` is symmetric, axisymmetric without swirl; `CartLiftIsTest`,
PartIII-b: smooth, `P`-periodic, bounded support). -/
def CartLiftRows : Prop :=
  ∀ (ε c P : ℝ), 0 < ε → 0 < c → P = 2 * ε * c → ∀ m : Chart → Ten3,
    IsTensorTest c (fun p => tv4 (m p)) →
      (∀ i, IsPhaseTest P (cartRowsC (cartLift ε⁻¹ c m) i)) ∧
        IsSymRows (cartRowsC (cartLift ε⁻¹ c m))

/-- **`PartII-a:N01/6` — the norm of the tensor lift** (lines 1644-1648: "the natural lifts
`b ↦ √s b` and `T ↦ sT` both multiply norms by `√π R`"; with the unnormalised `dq` of
`HTSpace` and the normalised phase measure of `Y₂` the factor is `R√(π/c)`, and `T_rz` counts
twice in the Frobenius norm): `√(Pε) ‖𝒩_T m‖_{Y₂(Sym₃)} ≤ √(2π) √2 ‖m‖_{H_T}`
(`R√(π/c) = √(2π)/√(Pε)` for `P = 2εc`, `R = ε⁻¹`). -/
def CartLiftNorm : Prop :=
  ∀ (ε c P : ℝ) [Fact (0 < P)], 0 < ε → 0 < c → P = 2 * ε * c → ∀ m : Chart → Ten3,
    IsTensorTest c (fun p => tv4 (m p)) → ∀ F : HTSpace c,
      (F : Profile → TensorVal) =ᵐ[measureHT c] (fun p => tv4 (m p)) →
        Real.sqrt (P * ε) * ‖smoothTensor P (cartRowsC (cartLift ε⁻¹ c m))‖ ≤
          Real.sqrt (2 * Real.pi) * Real.sqrt 2 * ‖F‖

/-- **`PartII-a:N01/7` — complex tensor tests are two real ones** (lines 1675, 1647-1650:
`Sym₃`-valued tests, no component with one azimuthal index): `M = tv4 ∘ m₁ + i tv4 ∘ m₂`
with `m₁, m₂` real chart tensors whose components are smooth tensor tests, pointwise
`‖tv4 m_k‖ ≤ ‖M‖`, and `div_ε` is linear on them. -/
def TensorTestReIm : Prop :=
  ∀ c : ℝ, 0 < c → ∀ M : Profile → TensorVal, IsTensorTest c M →
    ∃ m₁ m₂ : Chart → Ten3,
      IsTensorTest c (fun p => tv4 (m₁ p)) ∧ IsTensorTest c (fun p => tv4 (m₂ p)) ∧
      (∀ p, M p = tv4 (m₁ p) + Complex.I • tv4 (m₂ p)) ∧
      (∀ p, ‖tv4 (m₁ p)‖ ≤ ‖M p‖) ∧ (∀ p, ‖tv4 (m₂ p)‖ ≤ ‖M p‖) ∧
      ∀ (ε : ℝ) (p : Profile), divEps ε M p =
        divEps ε (fun q => tv4 (m₁ q)) p + Complex.I • divEps ε (fun q => tv4 (m₂ q)) p

/-- **`PartII-a:N01/8` — completion from smooth tensors** (line 1675: "The tensor map means
completion from smooth tensors"): if `‖T(s div_ε M)‖_H ≤ K‖M‖_{H_T}` for every smooth tensor test
`M`, then `T s div_ε` extends to a bounded `S : H_T → H` (`IsStressMap`) with `‖S‖ ≤ K`.
(Smooth tests are dense, `Masked.tensorTestDense`; `s div_ε M ∈ H`, `Masked.tensorTestDivMem`;
well defined because the bound applied to `M - M'` kills the ambiguity.) -/
def StressCompletion : Prop :=
  ∀ (c ε : ℝ), 0 < c → ∀ (T : HSpace c MeridC →L[ℂ] HSpace c MeridC) (K : ℝ), 0 ≤ K →
    (∀ M : Profile → TensorVal, IsTensorTest c M → ∀ (F : HTSpace c) (G : HSpace c MeridC),
      (F : Profile → TensorVal) =ᵐ[measureHT c] M →
      (G : Profile → MeridC) =ᵐ[measureH c] (fun p => (p.1 : ℂ) • divEps ε M p) →
        ‖T G‖ ≤ K * ‖F‖) →
    ∃ S : HTSpace c →L[ℂ] HSpace c MeridC, IsStressMap c ε T S ∧ ∀ F, ‖S F‖ ≤ K * ‖F‖

/-- **The flat age-energy estimate on smooth tests** (intermediate, proved in
`Sub/N01/FlatReduction.lean`; lines 1684-1689: the flat equation `(∂_s + μ/s - νΔ)b = P_0 div_0 M`,
`b = T_0(s div_0 M) = R_0(μ)P_0(s div_0 M)`; pairing with `s^{-1/2} b̄` gives
`(Re μ + 1/4)‖b‖²_H + ν‖∇b‖²_{L²(s^{-1/2})} ≤ ‖M‖_{H_T}‖∇b‖`, so
`‖b‖_H ≤ (2√((Re μ + 1/4)ν))⁻¹ √2 ‖M‖_{H_T}`; stated with the weaker constant
`((Re μ + 1/4)ν)^{-1/2}`). -/
def FlatSmoothBound : Prop :=
  ∀ (ν c : ℝ) (hc : 0 < c), 0 < ν → ∀ μ : ℂ, 0 < μ.re + 1 / 4 →
    ∀ M : Profile → TensorVal, IsTensorTest c M → ∀ (F : HTSpace c) (G : HSpace c MeridC),
      (F : Profile → TensorVal) =ᵐ[measureHT c] M →
      (G : Profile → MeridC) =ᵐ[measureH c] (fun p => (p.1 : ℂ) • divEps 0 M p) →
        ‖T0flat hc ν μ G‖ ≤ (Real.sqrt ((μ.re + 1 / 4) * ν))⁻¹ * ‖F‖

/-- **`PartII-a:N01/12` — the dissipation part of `near:free-energy`** (lines 1679-1683, the term
`√ν ‖(Q_ε b, ∂_η b, ε b_r)‖_{H_T}`, read through the velocity lift `J_v = U ∘ J_ε`: up to the
factor `κ = ε√(c/π)`, `∇_y(J_v b)` is the lift of `(Q_ε b, ∂_η b, ε b_r)`; with `free:stress-energy`
`‖∇S_μT‖ ≤ ν⁻¹‖T‖`).  For smooth tests: the phase lift of `T_ε(s div_ε M)` has a distributional
gradient in `Y₂` with `Σ_j ‖∂_j‖ ≤ C ν⁻¹ ‖M‖_{H_T}`.  Not needed for `NearStressMapExists`;
recorded for the local regularity statements (`PartII-a:N05`). -/
def DissipationBound : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (ν ε c P : ℝ) [Fact (0 < P)] (hν : 0 < ν) (hε : 0 < ε) (hc : 0 < c)
    (hP : P = 2 * ε * c), P ≤ 1 → ∀ μ : ℂ, 0 < μ.re + 1 / 4 →
    ∀ U : B0223.X SpaceC P →ₗᵢ[ℂ] Yq P 2, IsPhaseLift ε P U →
    ∀ M : Profile → TensorVal, IsTensorTest c M → ∀ (F : HTSpace c) (G : HSpace c MeridC),
      (F : Profile → TensorVal) =ᵐ[measureHT c] M →
      (G : Profile → MeridC) =ᵐ[measureH c] (fun p => (p.1 : ℂ) • divEps ε M p) →
        ∃ g : Fin 3 → Yq P 2,
          HasGrad (U (B0223.liftVec hε hc hP (Teps hν hε hc hP μ G))) g ∧
            ∑ j, ‖g j‖ ≤ C * ν⁻¹ * ‖F‖

end UnforcedLeray.Short.PartIIa.N01
