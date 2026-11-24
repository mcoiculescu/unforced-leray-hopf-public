import UnforcedLeray.Short.PartIIIb.Concrete.ReturnOps
import UnforcedLeray.Short.PartIIIb.NearInst
import UnforcedLeray.Short.PartIIb.Defs

/-!
# The physical layer of the return instance: pins of the primary fields of `ReturnBase`

Source of record: `the November 2 reference manuscript` (73 pages).

`Concrete/ReturnOps.lean` gives the gain-normed spaces `VelG`, `SrcG`, `StrG`, the structure
`ReturnBase` and `ReturnBase.toOps`.  This file states, as `Prop`s over a `ReturnBase`, the source
definitions of its remaining primary fields, and reduces the three identities of the exact return
(`ReturnOps.WardStressNormal`, `ReturnOps.PhysAffineIdentity`, `ReturnOps.HNilpotent`) to named
leaf statements.

## Physical fields

All physical fields live in the similarity variables `(τ, y) ∈ ℝ × ℝ³` with period
`P = 2εc = 2c/R` (source 2667, 2685) and are compared with the chart coefficients of the spaces of
`ReturnOps.lean` by the natural lifts (source 2681-2689):

* `velPhys R c b` : `𝒩_v b = √s (b_r e_r + b_z e_z)` (`Axi.Nv` of the `q`-periodic extension
  `Axi.perExt`), complexified for the phase pairings `pairF` of `Cons/L2/BackgroundConcrete`;
* `strPhys R c g` : `𝒩_T g = s g` in Cartesian components (`NearInst.cartLift`);
* `coefOf R F` : the inverse direction, the chart coefficient `s^{-1/2}(F_r, F_z)` of a physical
  field read at azimuth `φ = 0`.

## Pins

* (a) `IsExactMultiplier B R V rb` : `M = M_U`, `U = V + r_b`: the thin component of `M w` is
  `v ⊗ w + w ⊗ v`, the repair component `v_b ⊗ w + w ⊗ v_b`, `v = s^{-1/2}V`, `v_b = s^{-1/2}r_b`
  (source 2669-2672, 2706, 3876-3877, 4147, 4163-4164, 5133-5139, 5779-5782); the gain-normed
  analogue of `NearInst.IsSplitMult`.
* (b) `IsBodyInverse B ε μ` : `R = R_μ = D_μ⁻¹ℙ`, `D_μ = ∂_τ - y·∇/2 - νΔ + μ - 1/2` (source
  4139-4146, 5781, 5820), i.e. `R f` is the free response `IIb.IsFreeResponse` (the projected
  equation `(μ + L)w = ℙf` on the graph `D_2`, `bg:common-body-graph`, source 1351-1362) of the
  lifted force.  `IsStressInverse B ε μ` : `S = S_μ = R_μℙ div` (source 4145, 1556-1572): `S T`
  is a distributional `Y_2` solution of `D_μ w = ℙ div 𝒩_T(T₁ + T₂)` with the exact Cartesian
  divergence (whose chart form is source 3898-3901).  Uniqueness among distributional `Y_2`
  solutions (source 1571) is the leaf `FreeWeakUniqueness`.
  `IsNearSplit B ε μ δ S` : `S_N = S_μ - S_far` with `S_far = 1_{s<S, t>e^δ s} S_μ` in its exact
  kernel realization (source 3902-3912; `IsFarMaskG` is `NearInst.IsFarMask` on the gain-normed
  spaces); `NearSNAgree B o` relates `B.SN` to the near operator `o.SN` of `NearInst.NearOps`
  (function level, the stress inverse acting on `T₁ + T₂`).
* (c) `IsWardPinned B ε μ hχo χy U p` : the Ward fields (source 4161-4303).  For the old source
  `χ_oT` (`chiOStr`, any representatives of its components): `W_μ` is the separated-kernel
  response `IIIa.sepW` (`sep:resolvent`, source 3611-3621, `W_μ = -S_μ(χ_oT)` on the young
  receiver), `X₀ = W_μ - W_{μ+1}`, `X = 𝒞_y X₀` with the outward primitive `Ψ_Z` and the stream
  cutoff `𝒞_y Z = χ_y Z + (χ_y'/r)Ψ_Z e_z` (source 4178-4186), `Y = D_{μ+1}X`, `h = [U, X]`
  (source 4171-4174), and the four-term unprojected residual `Ẽ_μ` (source 4276-4280).  `B.Ef T`
  is `Ẽ_μ[T]` itself: the body inverse `R` supplies the Leray projection (source 5820), so
  `R(Ef T) = R_μℙẼ_μ[T]` as in `ward:stress-normal` (source 4300-4303).
  (`StatementsA.WardFields` is not used: its `Dmu : Vel →ₗ Vel` would be a total linear map on
  `VelG`, whereas `D_μ` is unbounded; the fields are pinned by their source formulas instead.)
* (d) `IsRAPinned B ι χf ε μ` : `𝔯_A` (Lemma `ret:physical-affine`, source 5001-5008) is the
  exact unprojected residual of the proof (source 5022-5050):
  `𝔯_A = D_μĥ_A + div M_Uĥ_A - F_A - E_A - ∇_y(sΨ_A)`, `Ψ_A = Σ_j (A^y_mer x_j)·∇p_j`
  (source 5024), stated against every phase test.  On solenoidal tests the gradient drops out and
  this is `(L_{f,μ} + ℙ div M_U)ĥ_A = ℙ(F_A + E_A + 𝔯_A)`; against all tests it determines `𝔯_A`
  (the projected identity alone determines it only up to gradients).

## Reductions (compiled here)

* `ReturnBase.wardStressNormal_of` : `WardStressNormal` from the energy equation of
  `h + S_μM_U(Y+h)` (source 4287-4289), the body inverse and free weak uniqueness (4290-4303).
* `ReturnBase.physAffineIdentity_of` : `PhysAffineIdentity` from the `𝔯_A` pin, the stress and
  body inverses, solenoidality of `ĥ_A` (source 4995-4997), additivity of the weak formulation and
  uniqueness.
* `HOldKernel` and `hNilpotent_of_kernel` : "`H` depends only on `χ_oT` and has young support, so
  `H² = 0`" (source 4313-4322, 5810-5811).  NB: `StatementsA.HOldDependence` (`H T = H(χ_oT)`) is
  not the source's statement and fails for the smooth cutoff `chiOStr` (`χ_o² ≠ χ_o`); the source's
  "depends only on `χ_oT`" is `χ_oT = 0 → HT = 0`, which suffices for `H² = 0`.
* `ReturnBase.hOldKernel_of`, `ReturnBase.hYoungSupport_of` (with `wardYoung_of`, `hAYoung_of`)
  and the assembly `ReturnBase.wardAffineNilpotent_of`.

The leaves (`FreeWeakUniqueness`, `WeakDmuAdd`, `WardEnergyEquation`, `HhatSolenoidal`,
`WardFieldsZero`, `WardYoungPointwise`, `HhatYoungPointwise`, `ChiOMultYoung`) are tasks; the
old-data dependence `IsLjOld` of `𝓛` comes from the `𝓛` pin of `ORG:return-concrete/source-L`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest)

/-! ## 1. Pointwise calculus in the similarity variables -/

/-- `∂_j f` of a spatial vector field. -/
def physPd (f : Space → Space) (j : Fin 3) (y : Space) : Space :=
  fderiv ℝ f y (coordinateVector j)

/-- `∂_j ∂_l f`. -/
def physPd2 (f : Space → Space) (j l : Fin 3) (y : Space) : Space :=
  physPd (fun y' => physPd f l y') j y

/-- `Δ_y f`. -/
def physLap (f : Space → Space) (y : Space) : Space := ∑ j : Fin 3, physPd2 f j j y

/-- `∇_y q` of a scalar. -/
def physGrad (q : Space → ℝ) (y : Space) : Space :=
  WithLp.toLp 2 fun j => fderiv ℝ q y (coordinateVector j)

/-- `D_μ X = ∂_τX - ½ y·∇X - νΔX + (μ - ½)X` (source 4140-4141). -/
def physDmu (ν μ : ℝ) (X : ℝ → Space → Space) (τ : ℝ) (y : Space) : Space :=
  deriv (fun t => X t y) τ - (1 / 2 : ℝ) • fderiv ℝ (X τ) y y - ν • physLap (X τ) y +
    (μ - 1 / 2) • X τ y

/-- The exact background `U` and its full pressure `p` (source 4139-4141): smooth on `ℝ × ℝ³`,
`P`-periodic in the phase (normalized phase measure `dτ/P`, source 4143), `div U = 0` and
`D₀U + U·∇U + ∇p = 0` pointwise (unforced profile equation, `μ = 0`). -/
structure IsExactProfile (ν P : ℝ) (U : ℝ → SpatialField) (p : ℝ → Space → ℝ) : Prop where
  periodicU : ∀ τ y, U (τ + P) y = U τ y
  periodicP : ∀ τ y, p (τ + P) y = p τ y
  smoothU : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun x : ℝ × Space => U x.1 x.2
  smoothP : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun x : ℝ × Space => p x.1 x.2
  div_free : ∀ τ y, ∑ j : Fin 3, physPd (U τ) j y j = 0
  equation : ∀ τ y, physDmu ν 0 U τ y + fderiv ℝ (U τ) y (U τ y) + physGrad (p τ) y = 0

/-- The chart coefficient `s^{-1/2}(F_r, F_z)` of an axisymmetric physical field `F`, read at the
chart point `(s, (q, η))`: at `y = (R/√s, 0, η/√s)` (azimuth `φ = 0`, `e_r = e_1`) and
`τ = 2q/R + log s` (inverse of `𝒩_v b = √s b`, source 2666-2668, 2683). -/
def coefOf (R : ℝ) (F : ℝ → Space → Space) (p : Chart) : Merid :=
  (Real.sqrt p.1)⁻¹ • !₂[F (NearInst.chartTau R p) (NearInst.chartY R p) 0,
    F (NearInst.chartTau R p) (NearInst.chartY R p) 2]

theorem coefOf_zero (R : ℝ) : coefOf R 0 = 0 := by
  funext p
  have h : (!₂[(0 : ℝ), 0] : Merid) = 0 := by
    ext i; fin_cases i <;> rfl
  simp only [coefOf, Pi.zero_apply, PiLp.zero_apply]
  rw [h, smul_zero]

/-! ## 2. Lifts and pairings -/

/-- The physical velocity `𝒩_v b = √s (b_r e_r + b_z e_z)` of a chart coefficient (periodically
extended in `q`, complexified), on `ℝ × ℝ³` (source 2683; `Axi.Nv`, `Axi.perExt`). -/
def velPhys (R c : ℝ) (b : Chart → Merid) : ℝ × Space → CVec3 :=
  fun x => B0412.realC (Nv R (perExt c b) x.1 x.2)

section Lifts

variable {c mZ ρb γ ν : ℝ}

/-- The sum `T₁ + T₂` of the two stress components (source 2700, 5777: the tensor inverse acts on
the sum of the thin and repair components). -/
def strSum (T : StrG c mZ ρb γ ν) : Chart → Ten3 :=
  fun p => (T.fst : Chart → Ten3) p + (T.snd : Chart → Ten3) p

end Lifts

/-- The physical tensor `𝒩_T g = s g` of a chart tensor, in Cartesian components (source 2683;
`NearInst.cartLift`). -/
def strPhys (R c : ℝ) (g : Chart → Ten3) : ℝ × Space → Matrix (Fin 3) (Fin 3) ℝ :=
  fun x => NearInst.cartLift R c g x.1 x.2

/-- `⟨T, ∇Φ⟩ = P⁻¹∫₀ᴾ∫ Σ_{ij} T_ij ∂_jΦ_i`, so that `⟨div T, Φ⟩ = -stressPair P T Φ`. -/
def stressPair (P : ℝ) (Tp : ℝ × Space → Matrix (Fin 3) (Fin 3) ℝ) (Φ : ℝ × Space → CVec3) :
    ℂ :=
  phaseInt P fun x => ∑ i : Fin 3, ∑ j : Fin 3, ((Tp x i j : ℝ) : ℂ) * dy j Φ x i

/-- `⟨q, div Φ⟩`, so that `⟨∇q, Φ⟩ = -scalarPair P q Φ`. -/
def scalarPair (P : ℝ) (q : ℝ × Space → ℝ) (Φ : ℝ × Space → CVec3) : ℂ :=
  phaseInt P fun x => ((q x : ℝ) : ℂ) * ∑ j : Fin 3, dy j Φ x j

theorem scalarPair_sol {P : ℝ} (q : ℝ × Space → ℝ) {Φ : ℝ × Space → CVec3}
    (hΦ : IsSolTest P Φ) : scalarPair P q Φ = 0 := by
  have h : (fun x : ℝ × Space => ((q x : ℝ) : ℂ) * ∑ j : Fin 3, dy j Φ x j) = fun _ => 0 := by
    funext x; rw [hΦ.2 x, mul_zero]
  unfold scalarPair
  rw [h]
  simp [UnforcedLeray.Cons.C03.Concrete.phaseInt]

/-- `w` is weakly solenoidal: `⟨∇φ, w⟩ = 0` for every scalar phase test. -/
def IsWeakSolenoidal (P : ℝ) (w : ℝ × Space → CVec3) : Prop :=
  ∀ φ : ℝ × Space → ℂ, IsPhaseTest P φ → pairF P (gradT φ) w = 0

/-- `w` is a weakly solenoidal distributional solution of `D_μ w = ℙ(rhs)`: for every solenoidal
phase test `Φ`, `⟨D_μᵗΦ, w⟩ = rhs Φ`, `D_μᵗ = L₀ᵗ + μ` (the Leray projection is invisible on
solenoidal tests).  Same clauses as `IIb.IsFreeResponse`. -/
structure IsWeakDmu (ν μ P : ℝ) (w : ℝ × Space → CVec3) (rhs : (ℝ × Space → CVec3) → ℂ) :
    Prop where
  solenoidal : IsWeakSolenoidal P w
  equation : ∀ Φ, IsSolTest P Φ → pairF P (fun x => L0T ν Φ x + (μ : ℂ) • Φ x) w = rhs Φ

/-! ## 3. Pins (a), (b): the exact multiplier and the free inverses -/

section Pins

variable {c mZ ρb γ ν : ℝ} {Aff : Type} [NormedAddCommGroup Aff] [NormedSpace ℝ Aff]
  [CompleteSpace Aff]

/-- **(a)** `M = M_U` with `U = V + r_b` (source 2669-2672, 2706, 3876-3877, 4147, 5133-5139,
5779-5782): the thin component of `M w` is `v ⊗ w + w ⊗ v`, the repair component
`v_b ⊗ w + w ⊗ v_b`, with the chart coefficients `v = s^{-1/2}V`, `v_b = s^{-1/2}r_b`
(`IIIa.chartCoeff`, radius `R = ε⁻¹`), order `(r, φ, z)`; the physical stress is
`𝒩_T(M w) = U ⊗ 𝒩_v w + 𝒩_v w ⊗ U` (source 4147). -/
def IsExactMultiplier (B : ReturnBase c mZ ρb γ ν Aff) (R : ℝ) (V rb : ℝ → SpatialField) :
    Prop :=
  ∀ w : VelG c γ ν,
    ((B.M w).fst : Chart → Ten3) =ᵐ[gainZ1Measure c mZ γ ν]
        (fun p => NearInst.ten3Of (IIIa.symOuter (IIIa.chartCoeff R V p) (w p))) ∧
      ((B.M w).snd : Chart → Ten3) =ᵐ[gainHTMeasure c ρb γ ν]
        (fun p => NearInst.ten3Of (IIIa.symOuter (IIIa.chartCoeff R rb p) (w p)))

/-- **(b)** The physical body inverse `R = R_μ = D_μ⁻¹ℙ` (source 4139-4146, 5781, 5820): for every
body force `f`, `R f` is the free response of the lifted force `𝒩_v f`, i.e. the solenoidal
solution in the graph `D_2` of `(μ + L)w = ℙ𝒩_v f`, `L = 𝒯 - νΔ - 1/2` (`IIb.IsFreeResponse`,
`bg:common-body-graph`, source 1351-1362), period `P = 2εc`, radius `R = ε⁻¹`. -/
def IsBodyInverse (B : ReturnBase c mZ ρb γ ν Aff) (ε μ : ℝ) : Prop :=
  ∀ f : SrcG c, IIb.IsFreeResponse ν (μ : ℂ) 2 (2 * ε * c) (velPhys ε⁻¹ c f)
    (velPhys ε⁻¹ c (B.R f))

/-- A stress inverse `S = R_μℙ div` (source 4145, `free:weak-stress` 1556-1572): for every stress
`T`, `S T` is a weakly solenoidal distributional `Y_2` solution of `D_μ w = ℙ div 𝒩_T(T₁ + T₂)`
with the exact Cartesian divergence (tensor partitions allowed before the divergence, 1572). -/
def IsWeakStressInverse (S : StrG c mZ ρb γ ν →L[ℝ] VelG c γ ν) (ε μ : ℝ) : Prop :=
  ∀ T : StrG c mZ ρb γ ν, IsWeakDmu ν μ (2 * ε * c) (velPhys ε⁻¹ c (S T))
    (fun Φ => -stressPair (2 * ε * c) (strPhys ε⁻¹ c (strSum T)) Φ)

/-- **(b)** `S = S_μ` (source 4145, 5781). -/
def IsStressInverse (B : ReturnBase c mZ ρb γ ν Aff) (ε μ : ℝ) : Prop :=
  IsWeakStressInverse B.S ε μ

/-- The far part `S_far = 1_{s<S, t>e^δ s} S_μ` on the gain-normed spaces, in its exact kernel
realization (source 3902-3912 with `sep:resolvent` 3621): `NearInst.IsFarMask` with `zsum`
replaced by `strSum`, pinned on the dense class `NearInst.IsBoxTensor`. -/
def IsFarMaskG (R μ δ Scut : ℝ) (Sf : StrG c mZ ρb γ ν →L[ℝ] VelG c γ ν) : Prop :=
  ∀ (F : StrG c mZ ρb γ ν) (f : Chart → Ten3), NearInst.IsBoxTensor f →
    strSum F =ᵐ[ageμ c (-1 / 2)] f →
    (Sf F : Chart → Merid) =ᵐ[ageμ c (-3 / 2)] fun p =>
      if p.1 < Scut then
        (Real.sqrt p.1)⁻¹ • NearInst.merRe (-NearInst.sepWfar ν (μ : ℂ) R δ p.1
          (NearInst.cartLift R c f) (NearInst.chartY R p) (NearInst.chartTau R p))
      else 0

/-- **(b)** `S_N = S_μ - S_far` (source 3911-3920, 5785): the near inverse is the full inverse
minus its masked far part with log gap `δ` and output cut `S`. -/
def IsNearSplit (B : ReturnBase c mZ ρb γ ν Aff) (ε μ δ Scut : ℝ) : Prop :=
  ∃ Sf : StrG c mZ ρb γ ν →L[ℝ] VelG c γ ν, IsFarMaskG ε⁻¹ μ δ Scut Sf ∧ B.SN = B.S - Sf

/-- `B.SN` is the near operator `o.SN` of `NearInst.NearOps` (`S_N = S_ε - S_far`, `S_ε` the
chart conjugate of `S_μ`, source 3888-3920), read at the level of functions: both act on the
sum of the two stress components. -/
def NearSNAgree (B : ReturnBase c mZ ρb γ ν Aff) (o : NearInst.NearOps c mZ ρb) : Prop :=
  ∀ (T : StrG c mZ ρb γ ν) (F : Zsp c mZ ρb), strSum T =ᵐ[ageμ c (-1 / 2)] NearInst.zsum F →
    (B.SN T : Chart → Merid) =ᵐ[ageμ c (-3 / 2)] (o.SN F : Chart → Merid)

end Pins

/-! ## 4. Pin (c): the Ward fields (source 4161-4303) -/

/-- The young stream cutoff profile `χ̂_y` (source 4164): `χ_y(s) = χ̂_y(νs)` equals one for
`s ≤ 0.8/ν` and vanishes for `s ≥ 1/ν`; `C^∞`. -/
structure IsYoungCutoff (χ : ℝ → ℝ) : Prop where
  smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ
  one : ∀ t, t ≤ 4 / 5 → χ t = 1
  zero : ∀ t, 1 ≤ t → χ t = 0
  range : ∀ t, 0 ≤ χ t ∧ χ t ≤ 1

/-- The physical old source `𝒩_T(χ_oT)` from a chart representative `g` of `χ_o(T₁ + T₂)`
(source 4171-4174: the full repair stress enters before inversion). -/
def oldPhys (R c : ℝ) (g : Chart → Ten3) : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ :=
  fun τ z => NearInst.cartLift R c g τ z

/-- `X₀ = W_μ - W_{μ+1}` (source 4171), `W_μ = -S_μ(χ_oT)` in its separated-kernel realization
`IIIa.sepW` (`sep:resolvent`, source 3611-3621; the tensor is identical in both resolvents),
real Cartesian components. -/
def wardX0 (ν μ R c : ℝ) (g : Chart → Ten3) (τ : ℝ) (y : Space) : Space :=
  WithLp.toLp 2 fun i =>
    (IIIa.sepW ν (μ : ℂ) (oldPhys R c g) y τ i -
      IIIa.sepW ν ((μ : ℂ) + 1) (oldPhys R c g) y τ i).re

/-- The outward primitive `Ψ_Z(r, z) = -∫_r^∞ ρ Z_z(ρ, z) dρ` (source 4178-4179), the field read
on the half plane `φ = 0`. -/
def outPrim (Z : ℝ → Space → Space) (τ r z : ℝ) : ℝ :=
  -∫ ρ in Ioi r, ρ * Z τ !₂[ρ, 0, z] 2

/-- The solenoidal stream cutoff `𝒞_y Z = χ_y Z + (χ_y'/r)Ψ_Z e_z` (source 4180-4186), with
`χ_y = χ̂_y(νR²/r²)` and `χ_y' = ∂_rχ_y = -2νR²r⁻³ χ̂_y'(νR²/r²)`, `r = |y'|`.  The time-dependent
Ward cutoff, on `Space`; the phase-free receiver cutoff of `𝓛` on `Vec3` is `streamCut` of
`Concrete/SourceL.lean`. -/
def wardStreamCut (ν R : ℝ) (χy : ℝ → ℝ) (Z : ℝ → Space → Space) (τ : ℝ) (y : Space) : Space :=
  χy (ν * age R y) • Z τ y +
    (deriv χy (ν * age R y) * (-2 * ν * R ^ 2 / ϱ y ^ 3) / ϱ y * outPrim Z τ (ϱ y) (y 2)) •
      coordinateVector 2

/-- `X = 𝒞_y X₀` (source 4171). -/
def wardX (ν μ R c : ℝ) (χy : ℝ → ℝ) (g : Chart → Ten3) : ℝ → Space → Space :=
  wardStreamCut ν R χy (wardX0 ν μ R c g)

/-- `Y = D_{μ+1}X` (source 4171). -/
def wardY (ν μ R c : ℝ) (χy : ℝ → ℝ) (g : Chart → Ten3) : ℝ → Space → Space :=
  physDmu ν (μ + 1) (wardX ν μ R c χy g)

/-- `h = [U, X] = U·∇X - X·∇U` (source 4171-4173). -/
def wardH (ν μ R c : ℝ) (χy : ℝ → ℝ) (U : ℝ → SpatialField) (g : Chart → Ten3) (τ : ℝ)
    (y : Space) : Space :=
  fderiv ℝ (wardX ν μ R c χy g τ) y (U τ y) - fderiv ℝ (U τ) y (wardX ν μ R c χy g τ y)

/-- `(C_diff)_i = Σ_{j,l}[(∂_jU_l)∂_{jl}X_i - (∂_jX_l)∂_{jl}U_i]` (source 4280-4282). -/
def physCdiff (U X : Space → Space) (y : Space) : Space :=
  ∑ j : Fin 3, ∑ l : Fin 3,
    ((physPd U j y) l • physPd2 X j l y - (physPd X j y) l • physPd2 U j l y)

/-- `(U ⊗ U) : D²X = Σ_{j,l} U_jU_l ∂_{jl}X`. -/
def physUUD2 (U X : Space → Space) (y : Space) : Space :=
  ∑ j : Fin 3, ∑ l : Fin 3, (U y j * U y l) • physPd2 X j l y

/-- `(DX + DXᵀ)∇p`, `(DX)_{ij} = ∂_jX_i`. -/
def physDXp (X : Space → Space) (q : Space → ℝ) (y : Space) : Space :=
  WithLp.toLp 2 fun i => ∑ j : Fin 3,
    (physPd X j y i + physPd X i y j) * fderiv ℝ q y (coordinateVector j)

/-- The full unprojected residual (source 4276-4280):
`Ẽ_μ = 2U·∇Y - 2νC_diff + (U⊗U):D²X - (DX + DXᵀ)∇p`, all four terms retained, `p` the exact
global pressure of `U`. -/
def wardE (ν μ R c : ℝ) (χy : ℝ → ℝ) (U : ℝ → SpatialField) (p : ℝ → Space → ℝ)
    (g : Chart → Ten3) (τ : ℝ) (y : Space) : Space :=
  (2 : ℝ) • fderiv ℝ (wardY ν μ R c χy g τ) y (U τ y) -
      (2 * ν) • physCdiff (U τ) (wardX ν μ R c χy g τ) y +
    physUUD2 (U τ) (wardX ν μ R c χy g τ) y - physDXp (wardX ν μ R c χy g τ) (p τ) y

section Ward

variable {c mZ ρb γ ν : ℝ} {Aff : Type} [NormedAddCommGroup Aff] [NormedSpace ℝ Aff]
  [CompleteSpace Aff]

/-- **(c)** The Ward fields of `B` (source 4161-4303): for every stress `T` and representatives
`g₁, g₂` of the two components of the old source `χ_oT` (`chiOStr`), the coefficients of
`B.Yf T`, `B.hf T`, `B.Ef T` are those of `Y = D_{μ+1}𝒞_y(W_μ - W_{μ+1})`, `h = [U, X]` and the
unprojected residual `Ẽ_μ` (`R` supplies `ℙ`, source 5820), on the background `U` with pressure
`p`, radius `R = ε⁻¹`. -/
def IsWardPinned (B : ReturnBase c mZ ρb γ ν Aff) (ε μ : ℝ) {χo : ℝ → ℝ}
    (hχo : IsOutwardCutoff χo) (χy : ℝ → ℝ) (U : ℝ → SpatialField) (p : ℝ → Space → ℝ) :
    Prop :=
  ∀ (T : StrG c mZ ρb γ ν) (g₁ g₂ : Chart → Ten3),
    ((chiOStr c mZ ρb γ ν hχo T).fst : Chart → Ten3) =ᵐ[gainZ1Measure c mZ γ ν] g₁ →
    ((chiOStr c mZ ρb γ ν hχo T).snd : Chart → Ten3) =ᵐ[gainHTMeasure c ρb γ ν] g₂ →
      (B.Yf T : Chart → Merid) =ᵐ[bodyMeasure c γ ν]
          coefOf ε⁻¹ (wardY ν μ ε⁻¹ c χy (g₁ + g₂)) ∧
        (B.hf T : Chart → Merid) =ᵐ[bodyMeasure c γ ν]
          coefOf ε⁻¹ (wardH ν μ ε⁻¹ c χy U (g₁ + g₂)) ∧
        (B.Ef T : Chart → Merid) =ᵐ[srcMeasure c]
          coefOf ε⁻¹ (wardE ν μ ε⁻¹ c χy U p (g₁ + g₂))

end Ward

/-! ## 5. Pin (d): the affine remainder `𝔯_A` (source 5001-5050) -/

/-- The lattice pressure potential `Ψ_A = Σ_j (A^y_mer x_j)·∇p_j` (source 5024). -/
def PsiA (ν : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (x : ℝ × ℝ) : ℝ :=
  ∑' j : ℤ, ((merApply (Ay ν χ A s) (xj ν j x)).1 * (mgrad (pj ν s j) x).1 +
    (merApply (Ay ν χ A s) (xj ν j x)).2 * (mgrad (pj ν s j) x).2)

/-- The global pressure scalar `sΨ_A` at the chart point of `(τ, y)` (source 5039-5043:
`s^{3/2}∇_{q,η}Ψ_A = ∇_y(sΨ_A) + εs^{3/2}(𝒦+2)Ψ_A e_r`). -/
def sPsiPhys (ν R : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (x : ℝ × Space) : ℝ :=
  (chart R x.1 x.2).1 * PsiA ν χ A (chart R x.1 x.2).1 (chart R x.1 x.2).2

section Affine

variable {c mZ ρb γ ν : ℝ} {Aff : Type} [NormedAddCommGroup Aff] [NormedSpace ℝ Aff]
  [CompleteSpace Aff]

/-- **(d)** `𝔯_A` is the exact unprojected residual of the proof of `ret:physical-affine`
(source 5001-5008, 5022-5050): `𝔯_A = D_μĥ_A + div M_Uĥ_A - F_A - E_A - ∇_y(sΨ_A)`, in
distributions against every phase test (`⟨D_μĥ, Φ⟩ = ⟨ĥ, D_μᵗΦ⟩`,
`⟨div M_Uĥ, Φ⟩ = -⟨M_Uĥ, ∇Φ⟩`, `⟨∇q, Φ⟩ = -⟨q, div Φ⟩`).  `ι` is the inclusion of `𝒜` into matrix
functions and `χf` the source cutoff profile, as in `IsAffinePinned`. -/
def IsRAPinned (B : ReturnBase c mZ ρb γ ν Aff) (ι : Aff →ₗ[ℝ] (ℝ → Mat3)) (χf : ℝ → ℝ)
    (ε μ : ℝ) : Prop :=
  ∀ (A : Aff) (Φ : ℝ × Space → CVec3), IsPhaseTest (2 * ε * c) Φ →
    pairF (2 * ε * c) (fun x => L0T ν Φ x + (μ : ℂ) • Φ x) (velPhys ε⁻¹ c (B.hA A)) -
        stressPair (2 * ε * c) (strPhys ε⁻¹ c (strSum (B.M (B.hA A)))) Φ =
      pairF (2 * ε * c) Φ (velPhys ε⁻¹ c ((B.FA A + B.EA A + B.rA A : SrcG c) : Chart → Merid)) -
        scalarPair (2 * ε * c) (sPsiPhys ν ε⁻¹ χf (ι A)) Φ

end Affine

/-! ## 6. Leaf statements -/

section Leaves

variable {c mZ ρb γ ν : ℝ} {Aff : Type} [NormedAddCommGroup Aff] [NormedSpace ℝ Aff]
  [CompleteSpace Aff]

/-- **Free weak uniqueness** (source 1571, `free:weak-stress`; homogeneous uniqueness of
`bg:common-body-graph`, 1351-1362, 1580-1583): two body velocities whose lifts are weakly
solenoidal distributional solutions of `D_μ w = ℙ(rhs)` with the same right side coincide. -/
def FreeWeakUniqueness (c γ ν ε μ : ℝ) : Prop :=
  ∀ (b b' : VelG c γ ν) (rhs : (ℝ × Space → CVec3) → ℂ),
    IsWeakDmu ν μ (2 * ε * c) (velPhys ε⁻¹ c b) rhs →
    IsWeakDmu ν μ (2 * ε * c) (velPhys ε⁻¹ c b') rhs → b = b'

/-- The weak formulation is additive along the lift of `VelG` (lift of an `Lp` sum, integrable
pairings). -/
def WeakDmuAdd (c γ ν ε μ : ℝ) : Prop :=
  ∀ (b b' : VelG c γ ν) (rhs rhs' : (ℝ × Space → CVec3) → ℂ),
    IsWeakDmu ν μ (2 * ε * c) (velPhys ε⁻¹ c b) rhs →
    IsWeakDmu ν μ (2 * ε * c) (velPhys ε⁻¹ c b') rhs' →
    IsWeakDmu ν μ (2 * ε * c) (velPhys ε⁻¹ c ((b + b' : VelG c γ ν) : Chart → Merid))
      (rhs + rhs')

/-- **The Ward energy equation** (source 4229-4289): the energy field `h + S_μM_U(Y + h)` is weakly
solenoidal and has distributional `D_μ` equal to `ℙẼ_μ`. -/
def WardEnergyEquation (B : ReturnBase c mZ ρb γ ν Aff) (ε μ : ℝ) : Prop :=
  ∀ T : StrG c mZ ρb γ ν,
    IsWeakDmu ν μ (2 * ε * c)
      (velPhys ε⁻¹ c ((B.hf T + B.S (B.M (B.Yf T + B.hf T)) : VelG c γ ν) : Chart → Merid))
      (fun Φ => pairF (2 * ε * c) Φ (velPhys ε⁻¹ c (B.Ef T)))

/-- `ĥ_A` is exactly solenoidal (source 4995-4997: stream function `rψ^p_A`). -/
def HhatSolenoidal (B : ReturnBase c mZ ρb γ ν Aff) (ε : ℝ) : Prop :=
  ∀ A : Aff, IsWeakSolenoidal (2 * ε * c) (velPhys ε⁻¹ c (B.hA A))

/-- With zero old source all Ward fields vanish (source 4171: `X₀` is linear in `χ_oT`). -/
def WardFieldsZero (ν μ R c : ℝ) (χy : ℝ → ℝ) (U : ℝ → SpatialField) : Prop :=
  wardY ν μ R c χy 0 = 0 ∧ wardH ν μ R c χy U 0 = 0

/-- Young support of `Y` and `h` (source 4306-4311): their coefficients vanish at ages
`s > 1/ν`. -/
def WardYoungPointwise (ν μ R c : ℝ) (χy : ℝ → ℝ) (U : ℝ → SpatialField) : Prop :=
  ∀ (g : Chart → Ten3) (p : Chart), 1 < ν * p.1 →
    coefOf R (wardY ν μ R c χy g) p = 0 ∧ coefOf R (wardH ν μ R c χy U g) p = 0

/-- Young support of `ĥ_A` (source 4953-4956, 4996: `A^y = χ_fA` vanishes for `s ≥ 1.1/ν`). -/
def HhatYoungPointwise (ν ε : ℝ) (χf : ℝ → ℝ) : Prop :=
  ∀ (A : ℝ → Mat3) (s : ℝ) (x : ℝ × ℝ), 11 / 10 < ν * s → hhatA ν ε χf A s x = 0

/-- A body velocity with young support: it vanishes at ages `s > 1.2/ν` (where `χ_o` may be
nonzero, source 4163). -/
def IsYoungVel (b : VelG c γ ν) : Prop :=
  ∀ᵐ p ∂(bodyMeasure c γ ν), 6 / 5 < ν * p.1 → (b : Chart → Merid) p = 0

theorem IsYoungVel.add {b b' : VelG c γ ν} (h : IsYoungVel b) (h' : IsYoungVel b') :
    IsYoungVel (b + b') := by
  filter_upwards [h, h', Lp.coeFn_add b b'] with p hp hp' hs hlt
  rw [hs, Pi.add_apply, hp hlt, hp' hlt, add_zero]

theorem IsYoungVel.sub {b b' : VelG c γ ν} (h : IsYoungVel b) (h' : IsYoungVel b') :
    IsYoungVel (b - b') := by
  filter_upwards [h, h', Lp.coeFn_sub b b'] with p hp hp' hs hlt
  rw [hs, Pi.sub_apply, hp hlt, hp' hlt, sub_zero]

/-- `χ_o` annihilates the multiplier of a young velocity (source 4310-4311, 4163). -/
def ChiOMultYoung (B : ReturnBase c mZ ρb γ ν Aff) {χo : ℝ → ℝ} (hχo : IsOutwardCutoff χo) :
    Prop :=
  ∀ w : VelG c γ ν, IsYoungVel w → chiOStr c mZ ρb γ ν hχo (B.M w) = 0

/-- `𝓛` depends only on old data (source 4762-4796, 5800-5803): `χ_oT = 0 → 𝓛T = 0`.  A
consequence of the `𝓛` pin of `ORG:return-concrete/source-L`. -/
def IsLjOld (B : ReturnBase c mZ ρb γ ν Aff) {χo : ℝ → ℝ} (hχo : IsOutwardCutoff χo) : Prop :=
  ∀ T : StrG c mZ ρb γ ν, chiOStr c mZ ρb γ ν hχo T = 0 → B.Lj T = 0

end Leaves

/-! ## 7. Nilpotency from old dependence (source 4313-4322, 5810-5811) -/

/-- "`H` depends only on `χ_oT`" (source 4313-4314, 5810): `χ_oT = 0 → HT = 0`. -/
def HOldKernel {Vel Str Src Aff Gam : Type}
    [NormedAddCommGroup Vel] [NormedSpace ℝ Vel] [NormedAddCommGroup Str] [NormedSpace ℝ Str]
    [NormedAddCommGroup Src] [NormedSpace ℝ Src] [NormedAddCommGroup Aff] [NormedSpace ℝ Aff]
    [CompleteSpace Aff] [NormedAddCommGroup Gam] [NormedSpace ℝ Gam] [CompleteSpace Gam]
    (o : ReturnOps Vel Str Src Aff Gam) (chiO : Str →ₗ[ℝ] Str) : Prop :=
  ∀ T, chiO T = 0 → o.Hop T = 0

/-- Old dependence and young support give `H² = 0` (source 4314-4316, 5811). -/
theorem hNilpotent_of_kernel {Vel Str Src Aff Gam : Type}
    [NormedAddCommGroup Vel] [NormedSpace ℝ Vel] [NormedAddCommGroup Str] [NormedSpace ℝ Str]
    [NormedAddCommGroup Src] [NormedSpace ℝ Src] [NormedAddCommGroup Aff] [NormedSpace ℝ Aff]
    [CompleteSpace Aff] [NormedAddCommGroup Gam] [NormedSpace ℝ Gam] [CompleteSpace Gam]
    (o : ReturnOps Vel Str Src Aff Gam) (chiO : Str →ₗ[ℝ] Str)
    (h1 : HOldKernel o chiO) (h2 : HYoungSupport o chiO) : o.HNilpotent :=
  fun T => h1 _ (h2 T)

/-! ## 8. The reductions -/

namespace ReturnBase

variable {c mZ ρb γ ν : ℝ} {Aff : Type} [NormedAddCommGroup Aff] [NormedSpace ℝ Aff]
  [CompleteSpace Aff] (B : ReturnBase c mZ ρb γ ν Aff)

/-- `D M v = M v + M S M v` for the instance. -/
theorem toOps_D_M (v : VelG c γ ν) :
    B.toOps.D (B.toOps.M v) = B.M v + B.M (B.S (B.M v)) := rfl

/-- `ward:stress-normal` (source 4290-4303): the energy equation, free weak uniqueness and the body
inverse give `h + S_μM_U(Y+h) = R_μℙẼ_μ`; multiplying by `M_U` and adding `M_UY` gives
`D M(Y + h) = MY + MR E`. -/
theorem wardStressNormal_of {ε μ : ℝ} (hE : WardEnergyEquation B ε μ)
    (hR : IsBodyInverse B ε μ) (hU : FreeWeakUniqueness c γ ν ε μ) :
    B.toOps.WardStressNormal := by
  intro T
  have hu : B.hf T + B.S (B.M (B.Yf T + B.hf T)) = B.R (B.Ef T) :=
    hU _ _ _ (hE T) ⟨(hR (B.Ef T)).solenoidal, (hR (B.Ef T)).equation⟩
  show B.toOps.D (B.toOps.M (B.Yf T + B.hf T)) = B.M (B.Yf T) + B.M (B.R (B.Ef T))
  rw [toOps_D_M, ← hu, map_add B.M (B.Yf T), map_add B.M (B.hf T)]
  abel

/-- `ret:physical-affine` in the form of source 5798 (`DMĥ_A = MR_μ(F_A + E_A + 𝔯_A)`): on
solenoidal tests the `𝔯_A` pin is the projected identity
`(L_{f,μ} + ℙ div M_U)ĥ_A = ℙ(F_A + E_A + 𝔯_A)`; adding the stress equation of `S_μM_Uĥ_A`
and applying uniqueness gives `ĥ_A + S_μM_Uĥ_A = R_μ(F_A + E_A + 𝔯_A)`. -/
theorem physAffineIdentity_of {ε μ : ℝ} {ι : Aff →ₗ[ℝ] (ℝ → Mat3)} {χf : ℝ → ℝ}
    (hrA : IsRAPinned B ι χf ε μ) (hsol : HhatSolenoidal B ε) (hS : IsStressInverse B ε μ)
    (hR : IsBodyInverse B ε μ) (hAdd : WeakDmuAdd c γ ν ε μ)
    (hU : FreeWeakUniqueness c γ ν ε μ) : B.toOps.PhysAffineIdentity := by
  intro A
  set P := 2 * ε * c
  set f : SrcG c := B.FA A + B.EA A + B.rA A
  set Tp := strPhys ε⁻¹ c (strSum (B.M (B.hA A)))
  have h1 : IsWeakDmu ν μ P (velPhys ε⁻¹ c (B.hA A))
      (fun Φ => pairF P Φ (velPhys ε⁻¹ c f) + stressPair P Tp Φ) := by
    refine ⟨hsol A, fun Φ hΦ => ?_⟩
    have h := hrA A Φ hΦ.1
    rw [scalarPair_sol _ hΦ, sub_zero] at h
    exact eq_add_of_sub_eq h
  have h2 : IsWeakDmu ν μ P (velPhys ε⁻¹ c (B.S (B.M (B.hA A))))
      (fun Φ => -stressPair P Tp Φ) := hS (B.M (B.hA A))
  have h3 := hAdd _ _ _ _ h1 h2
  have h4 : ((fun Φ => pairF P Φ (velPhys ε⁻¹ c f) + stressPair P Tp Φ) +
      fun Φ => -stressPair P Tp Φ) = fun Φ => pairF P Φ (velPhys ε⁻¹ c f) := by
    funext Φ
    simp only [Pi.add_apply]
    ring
  rw [h4] at h3
  have hu : B.hA A + B.S (B.M (B.hA A)) = B.R f :=
    hU _ _ _ h3 ⟨(hR f).solenoidal, (hR f).equation⟩
  show B.toOps.D (B.toOps.M (B.hA A)) = B.M (B.R f)
  rw [toOps_D_M, ← hu, map_add]

/-- `H` depends only on `χ_oT` (source 4313-4314, 5810): if `χ_oT = 0` the Ward pins with the
zero representatives give `Y[T] = h[T] = 0`, and `𝓛T = 0`. -/
theorem hOldKernel_of {ε μ : ℝ} {χo : ℝ → ℝ} (hχo : IsOutwardCutoff χo) {χy : ℝ → ℝ}
    {U : ℝ → SpatialField} {p : ℝ → Space → ℝ} (hW : IsWardPinned B ε μ hχo χy U p)
    (hz : WardFieldsZero ν μ ε⁻¹ c χy U) (hL : IsLjOld B hχo) :
    HOldKernel B.toOps (chiOStr c mZ ρb γ ν hχo : StrG c mZ ρb γ ν →ₗ[ℝ] StrG c mZ ρb γ ν) := by
  intro T hT
  have hT' : chiOStr c mZ ρb γ ν hχo T = 0 := hT
  have h1 : ((chiOStr c mZ ρb γ ν hχo T).fst : Chart → Ten3) =ᵐ[gainZ1Measure c mZ γ ν] 0 := by
    rw [hT', WithLp.zero_fst]; exact Lp.coeFn_zero _ _ _
  have h2 : ((chiOStr c mZ ρb γ ν hχo T).snd : Chart → Ten3) =ᵐ[gainHTMeasure c ρb γ ν] 0 := by
    rw [hT', WithLp.zero_snd]; exact Lp.coeFn_zero _ _ _
  obtain ⟨hY, hh, -⟩ := hW T 0 0 h1 h2
  rw [add_zero, hz.1, coefOf_zero] at hY
  rw [add_zero, hz.2, coefOf_zero] at hh
  have hY0 : B.Yf T = 0 := Lp.ext (hY.trans (Lp.coeFn_zero _ _ _).symm)
  have hh0 : B.hf T = 0 := Lp.ext (hh.trans (Lp.coeFn_zero _ _ _).symm)
  show B.M (B.Yf T + B.hf T - B.hA (B.Lj T)) = 0
  rw [hY0, hh0, hL T hT', map_zero, add_zero, sub_zero, map_zero]

/-- Young support of the Ward fields from the pins (source 4306-4311). -/
theorem wardYoung_of {ε μ : ℝ} {χo : ℝ → ℝ} (hχo : IsOutwardCutoff χo) {χy : ℝ → ℝ}
    {U : ℝ → SpatialField} {p : ℝ → Space → ℝ} (hW : IsWardPinned B ε μ hχo χy U p)
    (hpt : WardYoungPointwise ν μ ε⁻¹ c χy U) (T : StrG c mZ ρb γ ν) :
    IsYoungVel (B.Yf T) ∧ IsYoungVel (B.hf T) := by
  obtain ⟨hY, hh, -⟩ := hW T _ _ EventuallyEq.rfl EventuallyEq.rfl
  constructor
  · filter_upwards [hY] with q hq hlt
    rw [hq]
    exact (hpt _ q (by linarith)).1
  · filter_upwards [hh] with q hq hlt
    rw [hq]
    exact (hpt _ q (by linarith)).2

theorem merOf_zero : merOf 0 = 0 := by
  ext i; fin_cases i <;> rfl

/-- Young support of `ĥ_A` from the affine pin (source 4996). -/
theorem hAYoung_of {ι : Aff →ₗ[ℝ] (ℝ → Mat3)} {χf : ℝ → ℝ} {μ ε : ℝ}
    (hAff : IsAffinePinned B ι χf μ ε) (hpt : HhatYoungPointwise ν ε χf) (A : Aff) :
    IsYoungVel (B.hA A) := by
  filter_upwards [(hAff A).1] with q hq hlt
  rw [hq, hpt _ _ _ (by linarith), smul_zero, merOf_zero]

/-- `H` has young support (source 4306-4311, 4318-4321): `HT = M(Y + h - ĥ_{𝓛T})` with all three
velocities supported in `s ≤ 1.1/ν`, where `χ_o = 0`. -/
theorem hYoungSupport_of {χo : ℝ → ℝ} (hχo : IsOutwardCutoff χo)
    (hY : ∀ T, IsYoungVel (B.Yf T)) (hh : ∀ T, IsYoungVel (B.hf T))
    (hA : ∀ A, IsYoungVel (B.hA A)) (hχM : ChiOMultYoung B hχo) :
    HYoungSupport B.toOps
      (chiOStr c mZ ρb γ ν hχo : StrG c mZ ρb γ ν →ₗ[ℝ] StrG c mZ ρb γ ν) := by
  intro T
  show chiOStr c mZ ρb γ ν hχo (B.M (B.Yf T + B.hf T - B.hA (B.Lj T))) = 0
  exact hχM _ (((hY T).add (hh T)).sub (hA _))

/-- **Assembly** of the three identities of the exact return used at source 5796-5811 from the
pins and the leaves. -/
theorem wardAffineNilpotent_of {ε μ : ℝ} {χo : ℝ → ℝ} (hχo : IsOutwardCutoff χo)
    {χy χf : ℝ → ℝ} {V rb : ℝ → SpatialField} {p : ℝ → Space → ℝ}
    {ι : Aff →ₗ[ℝ] (ℝ → Mat3)}
    (hR : IsBodyInverse B ε μ) (hS : IsStressInverse B ε μ)
    (hW : IsWardPinned B ε μ hχo χy (fun τ y => V τ y + rb τ y) p)
    (hAff : IsAffinePinned B ι χf μ ε) (hrA : IsRAPinned B ι χf ε μ) (hL : IsLjOld B hχo)
    (hE : WardEnergyEquation B ε μ) (hU : FreeWeakUniqueness c γ ν ε μ)
    (hAdd : WeakDmuAdd c γ ν ε μ) (hsol : HhatSolenoidal B ε)
    (hz : WardFieldsZero ν μ ε⁻¹ c χy (fun τ y => V τ y + rb τ y))
    (hYp : WardYoungPointwise ν μ ε⁻¹ c χy (fun τ y => V τ y + rb τ y))
    (hHp : HhatYoungPointwise ν ε χf) (hχM : ChiOMultYoung B hχo) :
    B.toOps.WardStressNormal ∧ B.toOps.PhysAffineIdentity ∧ B.toOps.HNilpotent :=
  ⟨B.wardStressNormal_of hE hR hU, B.physAffineIdentity_of hrA hsol hS hR hAdd hU,
    hNilpotent_of_kernel B.toOps _ (B.hOldKernel_of hχo hW hz hL)
      (B.hYoungSupport_of hχo (fun T => (B.wardYoung_of hχo hW hYp T).1)
        (fun T => (B.wardYoung_of hχo hW hYp T).2) (B.hAYoung_of hAff hHp) hχM)⟩

end ReturnBase

end UnforcedLeray.Short.PartIIIb.Concrete
