import UnforcedLeray.Short.PartIIIb.Proofs.Wiring.Sub.PartIIIb_IIIb_D5_bridge
import UnforcedLeray.Short.PartIIIb.Proofs.Wiring.Sub.PartIIIb_IIIb_D5_bridge_ball

/-!
# Reduction of `Wiring.ShortBgExactProfile` (`PartIII-b:IIIb-D5/bridge/org`)

Source of record: `the November 2 reference manuscript`, lines 117-118,
2026-2037, 2505-2561, 2607-2612, 2641-2642, 4139-4141.

At all large levels `n` of a short-background sequence `B : ℕ → Spine.ShortBackground`, the
contraction-ball theorems (`IIb.ballHeatRemainder_proof`, `IIb.strongAllOrders_of`,
`_root_.bgComovingFirstEquation_proof`, and `IIb.smoothLeraySliceRegularity_proof`) identify the
residual vector field `G(τ, y) := -(D₀ U(τ, y) + (U(τ) · ∇U(τ))(y))` with
`𝔓(U(τ) · ∇U(τ)) - U(τ) · ∇U(τ)`, placing every slice `G(τ)` in
`L²(ℝ³) ∩ L⁴(ℝ³) ⊆ L^{11/4}(ℝ³)`.

Defining the smooth `P_n`-periodic radial Poincaré potential
`pr(τ, y) := ∫ t in (0 : ℝ)..1, ⟪G(τ, t • y), y⟫`, `shortBgExactProfile_of` reduces
`ShortBgExactProfile` (composed by `PartIII-b:IIIb-D5/bridge` in
`Proofs/Wiring/BackgroundBridge.lean` via `backgroundBridge_of`) to three pure-analysis leaves:
1. `ShortBgExactProfileAux.PoincareIntervalSmooth` (`PartIII-b:IIIb-D5/bridge/1`): joint `C^∞`
   smoothness of `(τ, y) ↦ ∫ t in 0..1, ⟪G(τ, t • y), y⟫` when `G` is jointly `C^∞`;
2. `ShortBgExactProfileAux.WeakGradPoincareRecovery` (`PartIII-b:IIIb-D5/bridge/2`): when a smooth
   spatial field `G` is the weak gradient of `P₀ ∈ L²(ℝ³)`, its radial Poincaré potential `pr`
   satisfies `∇pr = G` pointwise and `pr - c ∈ L²(ℝ³)` for some constant `c : ℝ`;
3. `ShortBgExactProfileAux.SmoothSolenoidalAndStressGrad` (`PartIII-b:IIIb-D5/bridge/3`): for a
   smooth solenoidal `W^{2,4}(ℝ³)` slice `f` with `f ⊗ f ∈ L²(ℝ³)` and smooth `G =ᵐ 𝐏(f·∇f) - f·∇f`,
   `div f = 0` pointwise and `G` is the weak gradient of the Riesz pressure `stressPressureL2 f`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.Wiring

open UnforcedLeray UnforcedLeray.Blueprint UnforcedLeray.Blueprint.Planar
open UnforcedLeray.Cons.Data

namespace ShortBgExactProfileAux

/-- Spatial radial Poincaré potential `pr(y) = ∫₀¹ ⟪G(t y), y⟫ dt`. -/
def radialPoincare (G : SpatialField) (y : Space) : ℝ :=
  ∫ t in (0 : ℝ)..1, inner ℝ (G (t • y)) y

/-- Pointwise residual field `G(τ, y) = -(D₀ U(τ, y) + (U(τ) · ∇U(τ))(y))`. -/
def exactResidField (ν : ℝ) (U : ℝ → SpatialField) (τ : ℝ) (y : Space) : Space :=
  -(physDmu ν 0 U τ y + fderiv ℝ (U τ) y (U τ y))

/-- Spacetime radial Poincaré pressure `pr(τ) = radialPoincare (G(τ))`. -/
def poincarePressure (ν : ℝ) (U : ℝ → SpatialField) (τ : ℝ) : Space → ℝ :=
  radialPoincare (exactResidField ν U τ)

/-- **Leaf 1 (`PartIII-b:IIIb-D5/bridge/1`)**: parametric `C^∞` regularity of `radialPoincare`
for a jointly `C^∞` spacetime vector field `G`. Composed by `PartIII-b:IIIb-D5/bridge` via
`shortBgExactProfile_of`. -/
def PoincareIntervalSmooth : Prop :=
  ∀ G : ℝ → SpatialField,
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × Space => G x.1 x.2) →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × Space => radialPoincare (G x.1) x.2)

/-- **Leaf 2 (`PartIII-b:IIIb-D5/bridge/2`)**: radial Poincaré potential recovery and `L²` constant
shift for a smooth vector field `G : SpatialField` that equals the distributional gradient of an
`L²(ℝ³)` scalar `P₀`. Composed by `PartIII-b:IIIb-D5/bridge` via `shortBgExactProfile_of`. -/
def WeakGradPoincareRecovery : Prop :=
  ∀ (G : SpatialField) (P₀ : Space → ℝ),
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G →
    MemLp P₀ 2 volume →
    (∀ (j : Fin 3) (φ : Space → ℝ), IsSpatialTest φ →
      (∫ y : Space, G y j * φ y) = -∫ y : Space, P₀ y * spatialTestDerivative j φ y) →
    (∀ y : Space, physGrad (radialPoincare G) y = G y) ∧
      ∃ c : ℝ, MemLp (fun y : Space => radialPoincare G y - c) 2 volume

/-- **Leaf 3 (`PartIII-b:IIIb-D5/bridge/3`)**: classical divergence-free identity and weak
Riesz-pressure gradient relation for a smooth solenoidal `W^{2,4}(ℝ³)` slice `f` with `f ⊗ f ∈ L²`
and smooth `G =ᵐ 𝐏(f · ∇f) - f · ∇f`. Composed by `PartIII-b:IIIb-D5/bridge` via
`shortBgExactProfile_of`. -/
def SmoothSolenoidalAndStressGrad : Prop :=
  ∀ (f G : SpatialField) (C : ℝ) (hT : ColumnsL2 (tensorColumns f f)),
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G →
    IsSolenoidal f →
    eLpNorm f 4 volume ≤ ENNReal.ofReal C →
    eLpNorm (fun y => fderiv ℝ f y) 4 volume ≤ ENNReal.ofReal C →
    eLpNorm (fun y => iteratedFDeriv ℝ 2 f y) 4 volume ≤ ENNReal.ofReal C →
    G =ᵐ[volume] (fun y =>
      (UnforcedLeray.Leray.projection
        (UnforcedLeray.toL2 (fun y' => fderiv ℝ f y' (f y'))) : SpatialField) y -
        fderiv ℝ f y (f y)) →
    (∀ y : Space, ∑ j : Fin 3, physPd f j y j = 0) ∧
    (∀ (j : Fin 3) (φ : Space → ℝ), IsSpatialTest φ →
      (∫ y : Space, G y j * φ y) =
        -∫ y : Space, Cons.C03.Concrete.stressPressureL2 f hT y *
          spatialTestDerivative j φ y)

private theorem physLap_eq_spatialLaplacian (f : SpatialField) (y : Space) :
    physLap f y = IIb.spatialLaplacian f y := by
  unfold physLap physPd2 physPd IIb.spatialLaplacian IIb.dirSpatialJet coordinateVector
  rfl

private theorem top_ne_zero : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by decide

private theorem top_add_one_le :
    ((⊤ : ℕ∞) : WithTop ℕ∞) + 1 ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by decide

private theorem fderiv_uncurry_time {U : ℝ → SpatialField}
    (hU : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℝ × Space => U z.1 z.2))
    (τ : ℝ) (y : Space) :
    fderiv ℝ (fun z : ℝ × Space => U z.1 z.2) (τ, y) ((1 : ℝ), (0 : Space)) =
      deriv (fun t => U t y) τ := by
  have hf : HasFDerivAt (fun z : ℝ × Space => U z.1 z.2)
      (fderiv ℝ (fun z : ℝ × Space => U z.1 z.2) (τ, y)) (τ, y) :=
    (hU.differentiable top_ne_zero (τ, y)).hasFDerivAt
  have hi : HasDerivAt (fun t : ℝ => ((t, y) : ℝ × Space)) ((1 : ℝ), (0 : Space)) τ :=
    (hasDerivAt_id τ).prodMk (hasDerivAt_const τ y)
  exact (hf.comp_hasDerivAt τ hi).deriv.symm

private theorem fderiv_uncurry_space {U : ℝ → SpatialField}
    (hU : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℝ × Space => U z.1 z.2))
    (τ : ℝ) (y v : Space) :
    fderiv ℝ (fun z : ℝ × Space => U z.1 z.2) (τ, y) ((0 : ℝ), v) =
      fderiv ℝ (U τ) y v := by
  have hf : HasFDerivAt (fun z : ℝ × Space => U z.1 z.2)
      (fderiv ℝ (fun z : ℝ × Space => U z.1 z.2) (τ, y)) (τ, y) :=
    (hU.differentiable top_ne_zero (τ, y)).hasFDerivAt
  have hc := hf.comp y (hasFDerivAt_prodMk_right (𝕜 := ℝ) τ y)
  rw [show (U τ) = (fun z : ℝ × Space => U z.1 z.2) ∘ fun y' : Space => (τ, y') from rfl,
    hc.fderiv]
  rfl

private theorem contDiff_exactResidField (ν : ℝ) {U : ℝ → SpatialField}
    (hU : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × Space => U x.1 x.2)) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : ℝ × Space => exactResidField ν U x.1 x.2) := by
  have hFd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : ℝ × Space => fderiv ℝ (fun z : ℝ × Space => U z.1 z.2) x) :=
    hU.fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) top_add_one_le
  have hdt_eq : (fun x : ℝ × Space => deriv (fun t => U t x.2) x.1) =
      fun x : ℝ × Space => fderiv ℝ (fun z : ℝ × Space => U z.1 z.2) x ((1 : ℝ), (0 : Space)) :=
    funext fun ⟨τ, y⟩ => (fderiv_uncurry_time hU τ y).symm
  have hdt : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : ℝ × Space => deriv (fun t => U t x.2) x.1) := by
    rw [hdt_eq]
    exact hFd.clm_apply contDiff_const
  have hdr_eq : (fun x : ℝ × Space => fderiv ℝ (U x.1) x.2 x.2) =
      fun x : ℝ × Space => fderiv ℝ (fun z : ℝ × Space => U z.1 z.2) x ((0 : ℝ), x.2) :=
    funext fun ⟨τ, y⟩ => (fderiv_uncurry_space hU τ y y).symm
  have hdr : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : ℝ × Space => fderiv ℝ (U x.1) x.2 x.2) := by
    rw [hdr_eq]
    exact hFd.clm_apply (contDiff_const.prodMk contDiff_snd)
  have hU₁ : ∀ j : Fin 3, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : ℝ × Space => physPd (U x.1) j x.2) := fun j => by
    have heq : (fun x : ℝ × Space => physPd (U x.1) j x.2) =
        fun x : ℝ × Space =>
          fderiv ℝ (fun z : ℝ × Space => U z.1 z.2) x ((0 : ℝ), coordinateVector j) :=
      funext fun ⟨τ, y⟩ => (fderiv_uncurry_space hU τ y (coordinateVector j)).symm
    rw [heq]
    exact hFd.clm_apply contDiff_const
  have hU₂ : ∀ j : Fin 3, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : ℝ × Space => physPd2 (U x.1) j j x.2) := fun j => by
    have heq : (fun x : ℝ × Space => physPd2 (U x.1) j j x.2) =
        fun x : ℝ × Space =>
          fderiv ℝ (fun z : ℝ × Space => physPd (U z.1) j z.2) x ((0 : ℝ), coordinateVector j) :=
      funext fun ⟨τ, y⟩ =>
        (fderiv_uncurry_space (U := fun t y' => physPd (U t) j y') (hU₁ j) τ y
          (coordinateVector j)).symm
    rw [heq]
    exact ((hU₁ j).fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞))
      top_add_one_le).clm_apply contDiff_const
  have hlap : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : ℝ × Space => physLap (U x.1) x.2) :=
    ContDiff.sum fun j _ => hU₂ j
  have hconv_eq : (fun x : ℝ × Space => fderiv ℝ (U x.1) x.2 (U x.1 x.2)) =
      fun x : ℝ × Space => fderiv ℝ (fun z : ℝ × Space => U z.1 z.2) x ((0 : ℝ), U x.1 x.2) :=
    funext fun ⟨τ, y⟩ => (fderiv_uncurry_space hU τ y (U τ y)).symm
  have hconv : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : ℝ × Space => fderiv ℝ (U x.1) x.2 (U x.1 x.2)) := by
    rw [hconv_eq]
    exact hFd.clm_apply (contDiff_const.prodMk hU)
  have hdmu : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : ℝ × Space => physDmu ν 0 U x.1 x.2) := by
    unfold physDmu
    exact ((hdt.sub (hdr.const_smul (1 / 2 : ℝ))).sub (hlap.const_smul ν)).add
      (hU.const_smul ((0 : ℝ) - 1 / 2))
  unfold exactResidField
  exact (hdmu.add hconv).neg

private theorem periodic_exactResidField (ν P : ℝ) {U : ℝ → SpatialField}
    (hper : ∀ τ y, U (τ + P) y = U τ y) (τ : ℝ) (y : Space) :
    exactResidField ν U (τ + P) y = exactResidField ν U τ y := by
  have hfun : U (τ + P) = U τ := funext fun y' => hper τ y'
  have hcomp : (fun t => U (t + P) y) = fun t => U t y := funext fun t => hper t y
  have hdt : deriv (fun t => U t y) (τ + P) = deriv (fun t => U t y) τ :=
    (deriv_comp_add_const (fun t => U t y) P τ).symm.trans (congrArg (fun g => deriv g τ) hcomp)
  simp only [exactResidField, physDmu, hdt, hfun]

private theorem periodic_poincarePressure (ν P : ℝ) {U : ℝ → SpatialField}
    (hper : ∀ τ y, U (τ + P) y = U τ y) (τ : ℝ) (y : Space) :
    poincarePressure ν U (τ + P) y = poincarePressure ν U τ y := by
  have heq : exactResidField ν U (τ + P) = exactResidField ν U τ :=
    funext fun y' => periodic_exactResidField ν P hper τ y'
  rw [poincarePressure, poincarePressure, heq]

private theorem exactResidField_eq_convectiveLeray_sub {ν : ℝ} {U L : ℝ → SpatialField}
    (hpt : ∀ τ y, deriv (fun t => U t y) τ - (1 / 2 : ℝ) • fderiv ℝ (U τ) y y =
      ν • IIb.spatialLaplacian (U τ) y + (1 / 2 : ℝ) • U τ y - L τ y)
    (τ : ℝ) (y : Space) :
    exactResidField ν U τ y = L τ y - fderiv ℝ (U τ) y (U τ y) := by
  have h1 := hpt τ y
  rw [← physLap_eq_spatialLaplacian] at h1
  unfold exactResidField physDmu
  have hd : deriv (fun t => U t y) τ =
      (1 / 2 : ℝ) • fderiv ℝ (U τ) y y +
        (ν • physLap (U τ) y + (1 / 2 : ℝ) • U τ y - L τ y) :=
    sub_eq_iff_eq_add'.mp h1
  rw [hd]
  ext i
  simp only [PiLp.neg_apply, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  ring

private theorem memLp_eleven_quarters_of_two_four {g : SpatialField}
    (hg : Continuous g) (h2 : MemLp g 2 volume) (h4 : MemLp g 4 volume) :
    MemLp g (11 / 4) volume := by
  have hp0 : (11 / 4 : ℝ≥0∞) ≠ 0 := by norm_num
  have hptop : (11 / 4 : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.div_ne_top ENNReal.coe_ne_top (by norm_num)
  have htoReal : (11 / 4 : ℝ≥0∞).toReal = 11 / 4 := by norm_num
  have h2int : Integrable (fun y : Space => ‖g y‖ ^ (2 : ℝ)) volume := by
    have := h2.integrable_norm_rpow (by norm_num) ENNReal.ofNat_ne_top
    simpa using this
  have h4int : Integrable (fun y : Space => ‖g y‖ ^ (4 : ℝ)) volume := by
    have := h4.integrable_norm_rpow (by norm_num) ENNReal.ofNat_ne_top
    simpa using this
  rw [← integrable_norm_rpow_iff hg.aestronglyMeasurable hp0 hptop, htoReal]
  refine (h2int.add h4int).mono'
    (hg.norm.rpow_const fun _ => Or.inr (by norm_num)).aestronglyMeasurable ?_
  filter_upwards [] with y
  dsimp only [Pi.add_apply]
  have hn : 0 ≤ ‖g y‖ := norm_nonneg _
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hn _)]
  by_cases hle : ‖g y‖ ≤ 1
  · by_cases h0 : ‖g y‖ = 0
    · simp [h0]
    · have hpos : 0 < ‖g y‖ := lt_of_le_of_ne hn (Ne.symm h0)
      have h1 : ‖g y‖ ^ (11 / 4 : ℝ) ≤ ‖g y‖ ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge hpos hle (by norm_num)
      have h4nn : 0 ≤ ‖g y‖ ^ (4 : ℝ) := Real.rpow_nonneg hn 4
      linarith
  · have hge : 1 ≤ ‖g y‖ := le_of_not_ge hle
    have h1 : ‖g y‖ ^ (11 / 4 : ℝ) ≤ ‖g y‖ ^ (4 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hge (by norm_num)
    have h2nn : 0 ≤ ‖g y‖ ^ (2 : ℝ) := Real.rpow_nonneg hn 2
    linarith

private theorem exactProfile_slice
    (hRec : WeakGradPoincareRecovery)
    (hSlice : SmoothSolenoidalAndStressGrad)
    {ν Cu : ℝ} {U L : ℝ → SpatialField}
    (hU_slice : ∀ τ : ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (U τ))
    (hG_slice_smooth : ∀ τ : ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (exactResidField ν U τ))
    (hsol : ∀ τ, IsSolenoidal (U τ))
    (hT : ∀ τ, ColumnsL2 (tensorColumns (U τ) (U τ)))
    (hCu : ∀ τ : ℝ,
      eLpNorm (U τ) 4 volume ≤ ENNReal.ofReal Cu ∧
      eLpNorm (fun y => fderiv ℝ (U τ) y) 4 volume ≤ ENNReal.ofReal Cu ∧
      eLpNorm (fun y => iteratedFDeriv ℝ 2 (U τ) y) 4 volume ≤ ENNReal.ofReal Cu)
    (hF2 : ∀ τ : ℝ, MemLp (fun y => fderiv ℝ (U τ) y (U τ y)) 2 volume)
    (hF4 : ∀ τ : ℝ, MemLp (fun y => fderiv ℝ (U τ) y (U τ y)) 4 volume)
    (hL2 : ∀ τ : ℝ, MemLp (L τ) 2 volume)
    (hL4 : ∀ τ : ℝ, MemLp (L τ) 4 volume)
    (hLae : ∀ τ : ℝ, L τ =ᵐ[volume]
      ⇑(Leray.projection (toL2 (fun y => fderiv ℝ (U τ) y (U τ y)))))
    (hG_eq : ∀ τ : ℝ, exactResidField ν U τ =
      L τ - fun y => fderiv ℝ (U τ) y (U τ y))
    (τ : ℝ) :
    (∀ y : Space, ∑ j : Fin 3, physPd (U τ) j y j = 0) ∧
    (∀ y : Space, physGrad (poincarePressure ν U τ) y = exactResidField ν U τ y) ∧
    (∃ c : ℝ, MemLp (fun y : Space => poincarePressure ν U τ y - c) 2 volume) ∧
    MemLp (exactResidField ν U τ) (11 / 4) volume := by
  have hGae : exactResidField ν U τ =ᵐ[volume]
      fun y =>
        (Leray.projection (toL2 (fun y' => fderiv ℝ (U τ) y' (U τ y'))) :
          SpatialField) y - fderiv ℝ (U τ) y (U τ y) := by
    filter_upwards [hLae τ] with y hy
    have heqy := congrFun (hG_eq τ) y
    dsimp only [Pi.sub_apply] at heqy
    rw [heqy, hy]
  obtain ⟨hdiv, hweak⟩ := hSlice (U τ) (exactResidField ν U τ) Cu (hT τ)
    (hU_slice τ) (hG_slice_smooth τ) (hsol τ)
    (hCu τ).1 (hCu τ).2.1 (hCu τ).2.2 hGae
  obtain ⟨hgrad_eq, hcL2⟩ := hRec (exactResidField ν U τ)
    (Cons.C03.Concrete.stressPressureL2 (U τ) (hT τ))
    (hG_slice_smooth τ)
    (Lp.memLp (Cons.C03.Concrete.stressPressureL2 (U τ) (hT τ))) hweak
  have hG2 : MemLp (exactResidField ν U τ) 2 volume := by
    rw [hG_eq τ]
    exact (hL2 τ).sub (hF2 τ)
  have hG4 : MemLp (exactResidField ν U τ) 4 volume := by
    rw [hG_eq τ]
    exact (hL4 τ).sub (hF4 τ)
  exact ⟨hdiv, hgrad_eq, hcL2,
    memLp_eleven_quarters_of_two_four (hG_slice_smooth τ).continuous hG2 hG4⟩

private theorem contDiff_slice {F : ℝ → SpatialField}
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × Space => F x.1 x.2)) (τ : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (F τ) :=
  hF.comp (contDiff_const.prodMk contDiff_id)

private theorem exactProfile_of_field
    (hSmooth : PoincareIntervalSmooth)
    (hRec : WeakGradPoincareRecovery)
    (hSlice : SmoothSolenoidalAndStressGrad)
    {ν P Cu : ℝ} {U L : ℝ → SpatialField}
    (hperU : ∀ τ y, U (τ + P) y = U τ y)
    (hsmoothU : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × Space => U x.1 x.2))
    (hsol : ∀ τ, IsSolenoidal (U τ))
    (hT : ∀ τ, ColumnsL2 (tensorColumns (U τ) (U τ)))
    (hCu : ∀ τ : ℝ,
      eLpNorm (U τ) 4 volume ≤ ENNReal.ofReal Cu ∧
      eLpNorm (fun y => fderiv ℝ (U τ) y) 4 volume ≤ ENNReal.ofReal Cu ∧
      eLpNorm (fun y => iteratedFDeriv ℝ 2 (U τ) y) 4 volume ≤ ENNReal.ofReal Cu)
    (hF2 : ∀ τ : ℝ, MemLp (fun y => fderiv ℝ (U τ) y (U τ y)) 2 volume)
    (hF4 : ∀ τ : ℝ, MemLp (fun y => fderiv ℝ (U τ) y (U τ y)) 4 volume)
    (hL2 : ∀ τ : ℝ, MemLp (L τ) 2 volume)
    (hL4 : ∀ τ : ℝ, MemLp (L τ) 4 volume)
    (hLae : ∀ τ : ℝ, L τ =ᵐ[volume]
      ⇑(Leray.projection (toL2 (fun y => fderiv ℝ (U τ) y (U τ y)))))
    (hpt : ∀ τ y,
      deriv (fun t => U t y) τ - (1 / 2 : ℝ) • fderiv ℝ (U τ) y y =
        ν • IIb.spatialLaplacian (U τ) y + (1 / 2 : ℝ) • U τ y - L τ y) :
    ∃ pr : ℝ → Space → ℝ,
      IsExactProfile ν P U pr ∧
      ∀ τ : ℝ, (∃ c : ℝ, MemLp (fun y : Space => pr τ y - c) 2 volume) ∧
        MemLp (physGrad (pr τ)) (11 / 4) volume := by
  have hU_slice : ∀ τ : ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (U τ) :=
    contDiff_slice hsmoothU
  have hG_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : ℝ × Space => exactResidField ν U x.1 x.2) :=
    contDiff_exactResidField ν hsmoothU
  have hG_slice_smooth : ∀ τ : ℝ,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (exactResidField ν U τ) :=
    contDiff_slice hG_smooth
  have hG_eq : ∀ τ : ℝ, exactResidField ν U τ =
      L τ - fun y => fderiv ℝ (U τ) y (U τ y) := fun τ =>
    funext (exactResidField_eq_convectiveLeray_sub hpt τ)
  have hSliceData := exactProfile_slice hRec hSlice hU_slice hG_slice_smooth
    hsol hT hCu hF2 hF4 hL2 hL4 hLae hG_eq
  refine ⟨poincarePressure ν U,
    { periodicU := hperU
      periodicP := periodic_poincarePressure ν P hperU
      smoothU := hsmoothU
      smoothP := hSmooth (exactResidField ν U) hG_smooth
      div_free := fun τ y => (hSliceData τ).1 y
      equation := fun τ y => by
        rw [(hSliceData τ).2.1 y]
        unfold exactResidField
        exact add_neg_cancel _ },
    fun τ => ⟨(hSliceData τ).2.2.1, ?_⟩⟩
  have hpeq : physGrad (poincarePressure ν U τ) = exactResidField ν U τ :=
    funext (hSliceData τ).2.1
  rw [hpeq]
  exact (hSliceData τ).2.2.2

end ShortBgExactProfileAux

/-- **Conditional assembly of `ShortBgExactProfile`** from its three leaves (composed by
`PartIII-b:IIIb-D5/bridge` in `Proofs/Wiring/BackgroundBridge.lean`). -/
theorem shortBgExactProfile_of
    (hSmooth : ShortBgExactProfileAux.PoincareIntervalSmooth)
    (hRec : ShortBgExactProfileAux.WeakGradPoincareRecovery)
    (hSlice : ShortBgExactProfileAux.SmoothSolenoidalAndStressGrad) :
    ShortBgExactProfile := by
  intro R hR m dm dp C Sig N hm hdm h2m hdmlt hdpgt hSig B hB
  obtain ⟨hνpos, hνlim, hεpos, hlim⟩ := Spine.parameterAsymptotics R hR
  obtain ⟨ν₀, hν₀, hBall⟩ := ShortBgExactProfileAux.ballState_evol
    hSig hR.1.eigenpair hm hdm h2m (max C 1) N (lt_of_lt_of_le one_pos (le_max_right C 1))
  have hν_small : ∀ᶠ n : ℕ in atTop, Spine.nuSeq R n ≤ ν₀ :=
    ((tendsto_order.1 hνlim).2 _ hν₀).mono fun _ hn => hn.le
  have hloss : ∀ᶠ n : ℕ in atTop, Spine.lossExponent R n ∈ Icc dm dp :=
    hlim.eventually (Icc_mem_nhds hdmlt hdpgt)
  filter_upwards [hB, hν_small, hloss] with n hBn hνn hln
  have hpν : (B n).par.ν = Spine.nuSeq R n := hBn.nu_eq
  have hpε : (B n).par.ε = Spine.epsSeq R n := hBn.eps_eq
  have hpc : (B n).par.c = ((B n).par.ν ^ 2)⁻¹ := by
    rw [hBn.c_eq, hpν]
    unfold Train.per
    ring
  have hreg : IIb.BgRegime (B n).par (Spine.lossExponent R n) dm dp := by
    refine ⟨hdm, hln.1, hln.2, ?_, hpc, hBn.train_buc,
      PartI.trainStreamSmooth (B n).par.ν (B n).par.c (B n).par.ν_pos (B n).par.c_pos
        (B n).par.trainData hBn.train_buc⟩
    rw [hpε, hpν]
    show Spine.epsSeq R n =
      Real.exp (-(-(Spine.nuSeq R n) * Real.log (Spine.epsSeq R n)) / Spine.nuSeq R n)
    have hne : Spine.nuSeq R n ≠ 0 := (hνpos n).ne'
    have hdiv : -(-(Spine.nuSeq R n) * Real.log (Spine.epsSeq R n)) / Spine.nuSeq R n =
        Real.log (Spine.epsSeq R n) := by field_simp
    rw [hdiv, Real.exp_log (hεpos n)]
  have hzn : ‖(B n).z‖ ≤
      max C 1 * ((B n).par.ν ^ N)⁻¹ * Real.exp (m / (B n).par.ν) *
        (B n).par.ε ^ (3 / 11 : ℝ) := by
    refine hBn.ball.trans ?_
    rw [← hpν, ← hpε]
    unfold Spine.lossRadius
    have hfac : 0 ≤ ((B n).par.ν ^ N)⁻¹ * Real.exp (m / (B n).par.ν) *
        (B n).par.ε ^ (3 / 11 : ℝ) :=
      mul_nonneg (mul_nonneg (inv_nonneg.2 (pow_nonneg (B n).par.ν_pos.le N)) (Real.exp_pos _).le)
        (Real.rpow_nonneg (B n).par.ε_pos.le _)
    have hleC : C ≤ max C 1 := le_max_left C 1
    calc C * ((B n).par.ν ^ N)⁻¹ * Real.exp (m / (B n).par.ν) * (B n).par.ε ^ (3 / 11 : ℝ)
        = C * (((B n).par.ν ^ N)⁻¹ * Real.exp (m / (B n).par.ν) *
            (B n).par.ε ^ (3 / 11 : ℝ)) := by ring
      _ ≤ max C 1 * (((B n).par.ν ^ N)⁻¹ * Real.exp (m / (B n).par.ν) *
            (B n).par.ε ^ (3 / 11 : ℝ)) :=
          mul_le_mul_of_nonneg_right hleC hfac
      _ = max C 1 * ((B n).par.ν ^ N)⁻¹ * Real.exp (m / (B n).par.ν) *
            (B n).par.ε ^ (3 / 11 : ℝ) := by ring
  obtain ⟨⟨Cu, hCu⟩, hF2, hF4, L, hL2, hL4, hLae, hpt⟩ :=
    hBall (B n).par (Spine.lossExponent R n) hreg (hpν.trans_le hνn) hBn.ageCut_eq hBn.mode_eq
      (B n).z hBn.equation hzn hBn.smooth
  have hP_eq : Spine.shortPeriod (Spine.nuSeq R n) (Spine.epsSeq R n) =
      2 * retEps R.planar R.σ₀ n * cOf (retNu R.planar R.σ₀ n) := by
    show 2 * Spine.epsSeq R n * Train.per (Spine.nuSeq R n) = _
    rw [per_eq]
    rfl
  have hperU : ∀ τ y,
      (B n).U (τ + 2 * retEps R.planar R.σ₀ n * cOf (retNu R.planar R.σ₀ n)) y =
        (B n).U τ y := by
    intro τ y
    rw [← hP_eq]
    exact congrFun (hBn.b3.background_periodic τ) y
  have hpt' : ∀ τ y,
      deriv (fun t => (B n).U t y) τ - (1 / 2 : ℝ) • fderiv ℝ ((B n).U τ) y y =
        retNu R.planar R.σ₀ n • IIb.spatialLaplacian ((B n).U τ) y +
          (1 / 2 : ℝ) • (B n).U τ y - L τ y := by
    intro τ y
    have h := hpt τ y
    rw [hpν] at h
    exact h
  exact ShortBgExactProfileAux.exactProfile_of_field hSmooth hRec hSlice
    hperU hBn.smooth hBn.b3.background_solenoidal hBn.b3.products_L2
    hCu hF2 hF4 hL2 hL4 hLae hpt'

end UnforcedLeray.Short.PartIIIb.Concrete.Wiring
