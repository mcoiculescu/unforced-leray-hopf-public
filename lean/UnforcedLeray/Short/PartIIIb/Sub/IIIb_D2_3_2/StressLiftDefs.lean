import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Ward3
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.StressPairAE

/-!
# Decomposition of `WardStressLift` (source 4147, 4161-4174)

Source: `the November 2 reference manuscript`.
`WardStressLift` follows from three source facts:

* `WardVelPhysYH` (source 4161-4174): the physical velocity of `Yf T + hf T` is
  `realC (wardY + wardH)` a.e.;
* `CartLiftSymOuter` (source 4147, 2683): for an axisymmetric field `U` without swirl, periodic in
  `τ`, the physical lift of the chart tensor `U ⊗ w + w ⊗ U` is the Cartesian `symProd U (𝒩_v w)`;
* `StrSumExactAE` (source 4147, 2700): `strSum (M w)` is the chart tensor of `U ⊗ w + w ⊗ U`,
  a.e. for `ageμ c (-1/2)`;

together with the a.e.-invariance `NearInst.stressPairAE` of the stress pairing.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest)

section StressLift

variable {c mZ ρb γ ν : ℝ} {Aff : Type} [NormedAddCommGroup Aff] [NormedSpace ℝ Aff]
  [CompleteSpace Aff]

/-- **(a)** (source 4161-4174, third clause of `WardLifts`): under `IsWardPinned` and a
`SmoothWardInput`, the physical velocity of `Yf T + hf T` is `realC (wardY + wardH)` a.e. in
`ℝ × ℝ³` (the pinned coefficient formulas are their own lifts, `SmoothWardInput.liftYH`). -/
def WardVelPhysYH (B : ReturnBase c mZ ρb γ ν Aff) (_hc : 0 < c) (ε : ℝ) (_hε : 0 < ε)
    (_hν : 0 < ν) (μ : ℝ) {χo : ℝ → ℝ} (hχo : IsOutwardCutoff χo) (χy : ℝ → ℝ)
    (U : ℝ → SpatialField) (p : ℝ → Space → ℝ) : Prop :=
  IsWardPinned B ε μ hχo χy U p →
    ∀ (T : StrG c mZ ρb γ ν) (g₁ g₂ : Chart → Ten3),
      ((chiOStr c mZ ρb γ ν hχo T).fst : Chart → Ten3) =ᵐ[gainZ1Measure c mZ γ ν] g₁ →
      ((chiOStr c mZ ρb γ ν hχo T).snd : Chart → Ten3) =ᵐ[gainHTMeasure c ρb γ ν] g₂ →
      SmoothWardInput ν μ ε⁻¹ c χy U p (g₁ + g₂) →
        velPhys ε⁻¹ c (B.Yf T + B.hf T) =ᵐ[volume]
          fun x => B0412.realC (wardY ν μ ε⁻¹ c χy (g₁ + g₂) x.1 x.2 +
            wardH ν μ ε⁻¹ c χy U (g₁ + g₂) x.1 x.2)

/-- **(b)** (source 4147, 2683; cylindrical frame equivariance, `NearInst.cartLift`): for an
axisymmetric field `U` without swirl, `P`-periodic in `τ` (`P = 2c/R`), and any meridional chart
field `w`, the physical lift `cartLift` of the chart tensor `ten3Of (symOuter (chartCoeff R U p)
(w p))` is `U ⊗ 𝒩_v w + 𝒩_v w ⊗ U` in Cartesian components, at every `(τ, z)` (on the axis both
sides vanish since `age R z = R²/0 = 0` in Lean). -/
def CartLiftSymOuter (R c : ℝ) (U : ℝ → SpatialField) : Prop :=
  0 < R → 0 < c → (∀ τ, AxiNoSwirlPt (U τ)) → (∀ τ y, U (τ + 2 * c / R) y = U τ y) →
    ∀ (w : Chart → Merid) (τ : ℝ) (z : Space),
      NearInst.cartLift R c
        (fun p => NearInst.ten3Of (IIIa.symOuter (IIIa.chartCoeff R U p) (w p))) τ z =
        symProd (U τ z) (Nv R (perExt c w) τ z)

/-- **(c)** (source 4147, 2700, `IsExactMultiplier`): for an exact multiplier,
`strSum (M w) = ten3Of (symOuter (chartCoeff R (V + r_b)) w)` a.e. for `ageμ c (-1/2)` (both gain
component measures are mutually absolutely continuous with `ageμ c (-1/2)`; `chartCoeff` is
additive in the field and `symOuter` bilinear). -/
def StrSumExactAE (B : ReturnBase c mZ ρb γ ν Aff) (_hc : 0 < c) (_hρb : 0 < ρb) (ε : ℝ)
    (V rb : ℝ → SpatialField) : Prop :=
  IsExactMultiplier B ε⁻¹ V rb →
    ∀ w : VelG c γ ν,
      strSum (B.M w) =ᵐ[ageμ c (-1 / 2)]
        fun p => NearInst.ten3Of
          (IIIa.symOuter (IIIa.chartCoeff ε⁻¹ (fun τ y => V τ y + rb τ y) p) (w p))

/-- **(e)** (source 2666-2700): the coercion `VelG → (Chart → Merid)` is additive `ageμ c (-1/2)`
-a.e. (the body measure `π g⁻² ageμ c (-3/2)` has positive density, so `ageμ c (-1/2)` is
absolutely continuous with respect to it, and `Lp.coeFn_add` holds for it). -/
def VelAddAE (c γ ν : ℝ) : Prop :=
  ∀ u v : VelG c γ ν,
    ((u + v : VelG c γ ν) : Chart → Merid) =ᵐ[ageμ c (-1 / 2)]
      (u : Chart → Merid) + (v : Chart → Merid)

/-- The stress pairing sees only the `volume`-a.e. class of the Cartesian tensor. -/
theorem stressPair_congr_ae (P : ℝ) {Tp Tp' : ℝ × Space → Matrix (Fin 3) (Fin 3) ℝ}
    (h : ∀ᵐ x ∂(volume : Measure (ℝ × Space)), Tp x = Tp' x) (Φ : ℝ × Space → CVec3) :
    stressPair P Tp Φ = stressPair P Tp' Φ := by
  have h2 := Measure.ae_ae_of_ae_prod (μ := (volume : Measure ℝ)) (ν := (volume : Measure Space)) h
  unfold stressPair phaseInt
  refine congrArg _ (integral_congr_ae ?_)
  filter_upwards [ae_restrict_of_ae h2] with t ht
  refine integral_congr_ae ?_
  filter_upwards [ht] with y hy
  simp [hy]

theorem wardStressLift_of (B : ReturnBase c mZ ρb γ ν Aff) (hc : 0 < c) (hρb : 0 < ρb)
    {ε : ℝ} (hε : 0 < ε) (hν : 0 < ν) {μ : ℝ} {χo : ℝ → ℝ} (hχo : IsOutwardCutoff χo)
    (χy : ℝ → ℝ) (V rb : ℝ → SpatialField) (p : ℝ → Space → ℝ)
    (ha : WardVelPhysYH B hc ε hε hν μ hχo χy (fun τ y => V τ y + rb τ y) p)
    (hb : CartLiftSymOuter ε⁻¹ c (fun τ y => V τ y + rb τ y))
    (hcc : StrSumExactAE B hc hρb ε V rb) (hadd : VelAddAE c γ ν) :
    WardStressLift B hc ε hε hν μ hχo χy V rb p := by
  intro hM hax hper hW T g₁ g₂ hg1 hg2 hin Φ hΦ
  have hR : 0 < ε⁻¹ := inv_pos.2 hε
  have hP : 2 * c / ε⁻¹ = 2 * ε * c := by field_simp
  set w : VelG c γ ν := B.Yf T + B.hf T with hw
  set w2 : Chart → Merid := (B.Yf T : Chart → Merid) + (B.hf T : Chart → Merid) with hw2
  have hg : strSum (B.M w) =ᵐ[ageμ c (-1 / 2)] fun p => NearInst.ten3Of
      (IIIa.symOuter (IIIa.chartCoeff ε⁻¹ (fun τ y => V τ y + rb τ y) p) (w2 p)) := by
    filter_upwards [hcc hM w, hadd (B.Yf T) (B.hf T)] with p h1 h2
    rw [h1]
    simp only [hw]
    rw [h2]
  rw [NearInst.stressPairAE c ε hc hε _ _ hg Φ]
  have hv := ha hW T g₁ g₂ hg1 hg2 hin
  have hv' : ∀ᵐ x ∂(volume : Measure (ℝ × Space)),
      Nv ε⁻¹ (perExt c w2) x.1 x.2 =
        wardY ν μ ε⁻¹ c χy (g₁ + g₂) x.1 x.2 + wardH ν μ ε⁻¹ c χy
          (fun τ y => V τ y + rb τ y) (g₁ + g₂) x.1 x.2 := by
    filter_upwards [hv] with x hx
    have hx' : B0412.realC (Nv ε⁻¹ (perExt c w2) x.1 x.2) =
        B0412.realC (wardY ν μ ε⁻¹ c χy (g₁ + g₂) x.1 x.2 + wardH ν μ ε⁻¹ c χy
          (fun τ y => V τ y + rb τ y) (g₁ + g₂) x.1 x.2) := hx
    ext i
    have := congrArg (fun v => v i) hx'
    rw [B0412.realC_apply, B0412.realC_apply] at this
    exact Complex.ofReal_injective this
  refine stressPair_congr_ae _ ?_ Φ
  filter_upwards [hv'] with x hx
  have hb' := hb hR hc hax (fun τ y => by rw [hP]; exact hper τ y) w2 x.1 x.2
  show NearInst.cartLift ε⁻¹ c _ x.1 x.2 = _
  rw [hb', hx]

end StressLift

end UnforcedLeray.Short.PartIIIb.Concrete
