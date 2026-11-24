import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.LjOld.Reduction
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Isos

/-!
# `𝒦^flat = 𝓛𝔗` from the pins: the flat return is `𝓛` of the near flat column of `F_A`
(source 4761-4763, 4804-4806, 4109-4111, 5897-5899)

Source of record: `the November 2 reference manuscript` (73 pages).

`NearInst/Link/Clauses.lean` states the pin
`IsFlatColumnKflat B o R0 hν : B.Kflat = B.Lj ∘L o.flatColG γ hν R0 ∘L B.FA` (`𝒦^flat = 𝓛𝔗`,
`𝔗A = T₀F_A`, `T₀ = D₀⁻¹M₀R₀` the flat forced column on the return spaces).  This file derives it
(`isFlatColumnKflat_of`) from

* the `𝓛` pin `Concrete.IsSourceLPinned` (`ι(𝒦^flat A) = 𝓛(𝔗(ιA))`, `ι(𝓛T) = 𝓛(thin T)`,
  source 4792-4806) and the affine pin `Concrete.IsAffinePinned` (`F_A = s^{3/2}f_A`, read in the
  coefficient convention `b = s^{-1/2}·`(physical field), source 4980-4985, 2683);
* the flat pins of the near layer: `IsFlatMult o.M0 tr` (`M₀ u = (v⊗u + u⊗v, 0)`, 3876-3877),
  `IsFreeStress o.S0 ν μ` (3420-3440, 1686-1689), `IsBodyTransport R0 (T0flat …)`
  (`R₀ = (μ - A₀)⁻¹P₀`, 1655-1656, 1676), and `IsUnit o.D0` (`D₀ = I + M₀S₀` invertible,
  3880-3887);
* the pin `IsFlatDuhamelColumn` on the flat setting `S` carrying `𝔗` (below): its Duhamel stress
  readout `M_B = v⊗K_cξ_B + K_cξ_B⊗v` at `B = B_{μ,ν}[A]` (4596-4610) is the polarized stress of
  the zero-entrance forced column `b = R₀h - S₀M₀b` of the coefficient `h` of `F_A`;
* two Isos leaves (`ThinFlatColG`, `SrcCoefAE`), the receiver congruence `XmtCongr`
  (`Concrete/SourceL.lean`, task `PartIII-b:C/srcL/5`) and the proved `oldMeasureAC`.

## Normalization check (source 1650-1656, 2683, 4594-4596, 4957-4958, 4980-4985)

The flat return forces its column with the Gaussian age force
`f_B = -P₀Σ_j[(B_mer x_j)·∇V_j + BV_j]` (4594-4596), `B = B_{μ,ν}[A] = (A^y)' + μA^y/s`
(4757-4758): the column is `∂_sb + (μ/s)b - νΔb + P₀div(v⊗b + b⊗v) = f_B`, i.e.
`ξ_B(s) = s^{-μ}∫₀^s t^μ 𝒰(s,t) g_B(t) dt` (4610) with `g_B` the vorticity of `f_B` (4597-4608).
The physical force is `F_A = s^{3/2}f_A` with the same Gaussian sum `f_A` (4969-4985), so its
coefficient in `SrcG`/`Hsp` (`𝒩_v h = √s h`, 2683) is `h = s^{-1/2}F_A = s f_A` (`affCoef`).  The
flat body inverse is `R₀ = (μ - A₀)⁻¹P₀`, `A₀ = -s∂_s + νsΔ` (1650-1656), so `R₀(s g)` is the
causal solution of `(∂_s + μ/s - νΔ)b = P₀g` (`B0225.R0_Ms_ae`:
`R₀(M_s g)(s) = ∫₀^s (σ/s)^μ e^{ν(s-σ)Δ} g(σ) dσ`).  Hence the age force of the near flat column
with input `h = s f_A` is `s⁻¹P₀h = P₀f_A = f_{B[A]}`: the two normalizations agree, the factor `s`
of the coefficient being exactly the factor `s` of `A₀`; the projection `P₀` of `f_B` is supplied by
`T₀ = R₀P₀` (the forces are unprojected, 4989-4990).

## Import note

`Clauses.lean` imports `Concrete/PhysLayer.lean`, which still declares `Concrete.streamCut` like
`Concrete/SourceL.lean` (organizer `ORG:return-concrete/physical-layer/Lj-old/clash`), so this
file cannot import `Clauses.lean`.  The conclusion of `isFlatColumnKflat_of` is the body of
`IsFlatColumnKflat B o R0 hν` written out; a term of this type is accepted where
`IsFlatColumnKflat B o R0 hν` is expected (definitional unfolding).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Kflat

open UnforcedLeray.Short.PartIIIb.Concrete UnforcedLeray.Short.PartIIIb.NearInst

/-! ## 1. The coefficient of `F_A` -/

/-- The chart coefficient `h = s^{-1/2}F_A = s f_A` of the physical affine force
`F_A = s^{3/2}f_A` (source 4980-4985, coefficient convention `𝒩_v h = √s h`, 2683), `(r, z)`
components; the right side of the `F_A` clause of `Concrete.IsAffinePinned`. -/
def affCoef (ν μ : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3) : Chart → Merid :=
  fun p => merOf ((Real.sqrt p.1)⁻¹ • FA ν μ χf A p.1 p.2)

/-! ## 2. Leaves (Isos algebra) -/

/-- **The force `(√π)⁻¹ srcIso f ∈ H` is any representative of `f`** (source 2683-2689: the body
norm of `Src` is `R⁻¹‖𝒩_v f‖_{Y_2} = √π‖f‖_H`, `srcMeasure = π·s^{-3/2}dς`): if
`f =ᵐ[srcMeasure c] F` then `(√π)⁻¹ srcIso f =ᵐ[s^{-3/2}dς] F` (the measures `π·μ` and `μ` have the
same null sets; `coeFn_hOfSrc`). -/
def SrcCoefAE : Prop :=
  ∀ (c : ℝ) (f : SrcG c) (F : Chart → Merid), (f : Chart → Merid) =ᵐ[srcMeasure c] F →
    (((Real.sqrt Real.pi)⁻¹ • srcIso c f : Hsp c) : Chart → Merid) =ᵐ[ageμ c (-3 / 2)] F

/-- **The thin component of the flat column on the return spaces** (source 4109-4111, 5609,
2683-2689): `flatColG R0 f = (√π)⁻¹ strIso⁻¹ G⁻¹ D₀⁻¹M₀R₀ srcIso f` (`NearInst/Link/Isos.lean`)
is, as a function, the thin component of `D₀⁻¹M₀R₀h` with `h = (√π)⁻¹ srcIso f` the force `f`
itself in `H`: `strIso⁻¹` multiplies by `g` and `G⁻¹` by `g⁻¹` (`coeFn_strIso_symm_fst`,
`coeFn_gainLp_symm`), and the scalar `(√π)⁻¹` passes through the linear maps.  Equality a.e. for the
gain measure of `Z_1` (`gainZ1Measure ≪ z1Measure`, a `withDensity`). -/
def ThinFlatColG : Prop :=
  ∀ (c mZ ρb γ ν : ℝ) (hν : 0 < ν) (o : NearOps c mZ ρb) (R0 : Hsp c →L[ℝ] Hsp c) (f : SrcG c),
    thinRep (o.flatColG γ hν R0 f) =ᵐ[gainZ1Measure c mZ γ ν]
      fun p => Ten3.toMatrix
        (((Ring.inverse o.D0 (o.M0 (R0 ((Real.sqrt Real.pi)⁻¹ • srcIso c f)))).fst :
          Chart → Ten3) p)

/-! ## 3. The pin on the flat setting -/

/-- **`𝔗` is the flat forced column of `F_A`: the pin of the flat setting `S`** (source 4761-4763:
"`𝔗_{μ,ν}A` the complete flat stress of the zero-entrance forced column with Gaussian age force
`f_{B_{μ,ν}[A]}`. The actual cylinder train remains in this evolution"; 4596-4610: `ξ_B`,
`b_B = K_cξ_B`, `M_B = v⊗b_B + b_B⊗v`; 4109-4111: the same prescribed smooth Gaussian affine force
in both geometries; 5897-5899).

For the flat setting `S` of the actual train `tr` (`c = ν⁻²`, 4557): for every realization of the
flat near operators by their pins (`M₀` the train multiplier `IsFlatMult`, `S₀` the free causal
stress inverse `IsFreeStress`, `R₀` the flat body inverse `IsBodyTransport … T0flat`, `D₀ = I + M₀S₀`
invertible), every `A ∈ 𝒜` and every `h ∈ H` representing the coefficient `affCoef` of `F_A`, the
Duhamel stress readout `𝔗A = frakT S ν μ χf A` of `S` at `B_{μ,ν}[A]` equals, a.e. on the old
region `u > 1.2/ν` (where `𝓛` reads it, `oldMeasure`), the polarized stress `v⊗b + b⊗v` of the
zero-entrance forced column `b = R₀h - S₀M₀b` (the flat form of 4084-4086: `b = R₀f - S₀T₀`,
`T₀ = M₀b`, i.e. `∂_sb + (μ/s)b - νΔb + P₀div(v⊗b+b⊗v) = s⁻¹P₀h = f_{B[A]}`; normalization check in
the module docstring).  `S` is free data in `Concrete.IsSourceLPinned`; this pin identifies it with
the actual flat setting (construction: organizer `ORG:return-concrete/near/link/kflat/flat-setting`). -/
def IsFlatDuhamelColumn (S : ConcreteYF.FlatSetting) {c ν : ℝ} (hc : 0 < c)
    (tr : UnforcedLeray.B0140.TrainSol ν c) (μ as : ℝ) (χf : ℝ → ℝ) : Prop :=
  IsSourceCutoffC χf →
  ∀ (mZ ρb : ℝ) (o : NearOps c mZ ρb) (R0 : Hsp c →L[ℝ] Hsp c),
    IsFlatMult o.M0 tr → IsFreeStress o.S0 ν μ →
    IsBodyTransport R0 (UnforcedLeray.Short.PartIIa.T0flat hc ν (μ : ℂ)) → IsUnit o.D0 →
    ∀ A : ℝ → Mat3, IsAffElem as A → ∀ h b : Hsp c,
      (h : Chart → Merid) =ᵐ[ageμ c (-3 / 2)] affCoef ν μ χf A →
      b = R0 h - o.S0 (o.M0 b) →
      frakT S ν μ χf A =ᵐ[oldMeasure c ν]
        fun p => (UnforcedLeray.Short.IIIa.symOuter (trainMer tr p) (b p) : Mat3)

/-! ## 4. The forced column of the near operators -/

/-- With `D₀ = I + M₀S₀` invertible, `b = R₀h - S₀D₀⁻¹M₀R₀h` solves the forced-column equation
`b = R₀h - S₀M₀b`, and `M₀b = D₀⁻¹M₀R₀h` (source 3880, 4084-4086). -/
theorem flatColumn_solves {c mZ ρb : ℝ} (o : NearOps c mZ ρb) (R0 : Hsp c →L[ℝ] Hsp c)
    (hD0 : IsUnit o.D0) (h : Hsp c) :
    o.M0 (R0 h - o.S0 (Ring.inverse o.D0 (o.M0 (R0 h)))) = Ring.inverse o.D0 (o.M0 (R0 h)) ∧
      R0 h - o.S0 (Ring.inverse o.D0 (o.M0 (R0 h))) =
        R0 h - o.S0 (o.M0 (R0 h - o.S0 (Ring.inverse o.D0 (o.M0 (R0 h))))) := by
  set y := o.M0 (R0 h)
  set x := Ring.inverse o.D0 y
  have hDx : x + o.M0 (o.S0 x) = y := by
    have h1 := congrArg (fun T : Zsp c mZ ρb →L[ℝ] Zsp c mZ ρb => T y)
      (Ring.mul_inverse_cancel o.D0 hD0)
    simpa [NearOps.D0, x] using h1
  have hM : o.M0 (R0 h - o.S0 x) = x := by
    rw [map_sub]
    show y - o.M0 (o.S0 x) = x
    rw [← hDx]
    abel
  exact ⟨hM, by rw [hM]⟩

/-! ## 5. The assembly -/

/-- **`𝒦^flat = 𝓛 ∘ T₀ ∘ F` from the pins** (source 4761-4763, 4804-4806, 4109-4111,
5897-5899): the body of `IsFlatColumnKflat B o R0 hν` (`NearInst/Link/Clauses.lean`).

Proof: `ι` is injective; by `IsSourceLPinned`, `ι(𝒦^flat A) = 𝓛(𝔗(ιA))` and
`ι(𝓛T) = 𝓛(thin T)`; by `XmtCongr` and `Lpt_congr_Xmt` it suffices that `𝔗(ιA)` and the thin
component of `T₀F_A` agree a.e. on the old region.  With `h = (√π)⁻¹ srcIso F_A` (`= affCoef` a.e.
by `IsAffinePinned` and `SrcCoefAE`) and the forced column `b = R₀h - S₀D₀⁻¹M₀R₀h`
(`flatColumn_solves`), `IsFlatDuhamelColumn` gives `𝔗(ιA) = v⊗b + b⊗v`, `IsFlatMult` gives
`thin(D₀⁻¹M₀R₀h) = thin(M₀b) = v⊗b + b⊗v`, and `ThinFlatColG` gives
`thin(T₀F_A) = thin(D₀⁻¹M₀R₀h)`; the null sets are transferred by
`z1Measure ≫ gainZ1Measure ≫ oldMeasure` (`withDensity`, `oldMeasureAC`). -/
theorem isFlatColumnKflat_of (hT : ThinFlatColG) (hSrc : SrcCoefAE) (hXC : XmtCongr)
    {c mZ ρb γ ν : ℝ} {Aff : Type} [NormedAddCommGroup Aff] [NormedSpace ℝ Aff]
    [CompleteSpace Aff] (B : ReturnBase c mZ ρb γ ν Aff) (o : NearOps c mZ ρb)
    (R0 : Hsp c →L[ℝ] Hsp c) (hν : 0 < ν) (hc : 0 < c) {ι : Aff →ₗ[ℝ] (ℝ → Mat3)}
    (hι : Function.Injective ι) {as : ℝ} (hιA : ∀ A, IsAffElem as (ι A))
    {S : ConcreteYF.FlatSetting} {lam κ ell : ℂ} {J : ℂ → ℂ} {ε μ : ℝ} {χo χy χf : ℝ → ℝ}
    (hχo : IsOutwardCutoff χo) (hχf : IsSourceCutoffC χf)
    (hL : IsSourceLPinned B ι S lam κ ell J ε μ χo χy χf) (hF : IsAffinePinned B ι χf μ ε)
    (tr : UnforcedLeray.B0140.TrainSol ν c) (hM0 : IsFlatMult o.M0 tr)
    (hS0 : IsFreeStress o.S0 ν μ)
    (hR0 : IsBodyTransport R0 (UnforcedLeray.Short.PartIIa.T0flat hc ν (μ : ℂ)))
    (hD0 : IsUnit o.D0) (hS : IsFlatDuhamelColumn S hc tr μ as χf) :
    B.Kflat = B.Lj ∘L o.flatColG γ hν R0 ∘L B.FA := by
  ext1 A
  apply hι
  rw [hL.2.2.2 A, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hL.1]
  unfold KflatFun LjFun
  apply Lpt_congr_Xmt
  apply hXC c ν ε μ χo χy hχo hν
  set h : Hsp c := (Real.sqrt Real.pi)⁻¹ • srcIso c (B.FA A) with hh_def
  have hh : (h : Chart → Merid) =ᵐ[ageμ c (-3 / 2)] affCoef ν μ χf (ι A) :=
    hSrc c (B.FA A) _ (hF A).2.1
  obtain ⟨hMb, hb⟩ := flatColumn_solves o R0 hD0 h
  set b : Hsp c := R0 h - o.S0 (Ring.inverse o.D0 (o.M0 (R0 h))) with hb_def
  have h1 := hS hχf mZ ρb o R0 hM0 hS0 hR0 hD0 (ι A) (hιA A) h b hh hb
  have h2 : (((Ring.inverse o.D0 (o.M0 (R0 h))).fst : Chart → Ten3)) =ᵐ[z1Measure c mZ]
      fun p => ten3Of (UnforcedLeray.Short.IIIa.symOuter (trainMer tr p) (b p)) := by
    rw [← hMb]
    exact (hM0 b).1
  have h2' := (oldMeasureAC c mZ γ ν hν).ae_le
    ((withDensity_absolutelyContinuous (z1Measure c mZ) _).ae_le h2)
  have h3 := (oldMeasureAC c mZ γ ν hν).ae_le (hT c mZ ρb γ ν hν o R0 (B.FA A))
  filter_upwards [h1, h2', h3] with p hp1 hp2 hp3
  rw [hp1, hp3, hp2]
  rfl

end UnforcedLeray.Short.PartIIIb.NearInst.Kflat
