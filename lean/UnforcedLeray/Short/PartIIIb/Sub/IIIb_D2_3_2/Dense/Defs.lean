import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnOps.ChiOStrApply

/-!
# Decomposition of `WardSmoothDense` (`PartIII-b:IIIb-D2/3/2/11`, source 4284-4286)

Source: `the November 2 reference manuscript`.

"For actual graph inputs this identity holds distributionally by symmetry-preserving smooth
approximation of `w`, followed by the multiplier, moment, repair-product and separated-kernel
bounds" (4284-4286).  The smooth class is `SmoothWardSet` (`Defs.lean`): the stresses whose old
source `χ_oT` has representatives `g₁, g₂` with `g₁ + g₂` smooth old data (`IsSmoothOld`) whose
regularized Ward fields are smooth, periodic, solenoidal and lift their chart coefficients
(`SmoothWardInput`).  Density splits into

* (a) `StrSmoothDense`: the stresses with smooth representatives of compact support in the open
  chart domain are dense in `StrG` (a chart tensor lifts to an axisymmetric swirl-free tensor,
  source 121-124, 2683, so chart approximation preserves the symmetry); `chiOSmoothRep` (proved
  here): `χ_o` turns them into smooth old data (source 4163-4166);
* (b) the Ward fields of smooth old data: `WardXrSmoothData` (separated-kernel regularity of
  `X = 𝒞_y(W_μ - W_{μ+1})`, source 3604-3621, 4161-4186), `WardFieldsSmooth` (pointwise calculus),
  `WardFieldsAxi` (orthogonal maps fixing the axis commute with the Ward operations, source
  121-124, 6314-6316) and `AxiLiftOfAxi` (a periodic axisymmetric swirl-free field vanishing on the
  axis is the lift of its chart coefficient, source 2666-2689).  The periodicity of the fields
  (`wardFields_periodic`) and their vanishing near the axis (`physFields_eq_zero_of_nhds`) are
  proved here.

No decay or growth of the background enters (the weak equation is tested against phase tests of
bounded spatial support, `WardIBPLoc`).  The symmetry `AxiNoSwirlPt` of the background is a
hypothesis (source 121-124, 4144-4145).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest)

/-! ## 1. The leaves -/

/-- **(a) Density of smooth chart data** (source 4284-4286, 2697-2700): for `c, ν > 0` the
stresses both of whose components have smooth representatives with compact support inside the
open chart domain `chartDom c` are dense in `StrG`.  (The component measures `gainZ1Measure`,
`gainHTMeasure` are `ageμ c (-1/2)` with the continuous densities `W²g⁻²`, `ρ_b⁻¹g⁻²`; they are
finite on compacts of `Chart` and carried by `(0,∞) × [-c/2, c/2) × ℝ`, which `chartDom c` covers
up to the null seam `q = -c/2`.) -/
def StrSmoothDense (c mZ ρb γ ν : ℝ) : Prop :=
  0 < c → 0 < ν →
    Dense {T : StrG c mZ ρb γ ν | ∃ G₁ G₂ : Chart → Ten3,
      (T.fst : Chart → Ten3) =ᵐ[gainZ1Measure c mZ γ ν] G₁ ∧
      (T.snd : Chart → Ten3) =ᵐ[gainHTMeasure c ρb γ ν] G₂ ∧
      IsSmoothChart c G₁ ∧ IsSmoothChart c G₂}

/-- **(b1) The Ward displacement of smooth old data** (source 4161-4186, 3604-3621): for smooth old
data `g` (`IsSmoothOld`: the physical source `oldPhys R c g` is smooth, `2c/R`-periodic and
supported in the old disk `ϱ ≤ R√(5ν/6)`, compactly in `z`), the regularized displacement
`X = 𝒞_y(W_μ - W_{μ+1})` (`wardXr`) is jointly `C^∞`, `2c/R`-periodic, solenoidal, and
axisymmetric without swirl.  `W_μ` is the separated-kernel integral `IIIa.sepW` (`sep:resolvent`);
on `ϱ > R√(5ν/6)` its derivatives of every order are obtained by differentiating under the
integral, with `|D^j∇K_t(x)| ≤ C_j|x|^{-4-j}` (`sep:kernel`, `IIIa.SepKernelBounds`) and the radial
gap `|y - λz| ≥ ϱ(y) - λϱ(z)`; the same bounds make the outward primitive `Ψ_{X₀}` smooth and give
its stream relations (4177-4179); `𝒞_y` is solenoidal (4180-4186, `wardStreamCutDivFree_of`);
`wardXr` vanishes on `ϱ ≤ R√ν` (`wardXr_eq_zero_of_sq_le`). -/
def WardXrSmoothData : Prop :=
  ∀ (ν μ R c : ℝ) (χy : ℝ → ℝ), 0 < ν → 0 < R → 0 < c → -(1 / 4) < μ → IsYoungCutoff χy →
    ∀ g : Chart → Ten3, IsSmoothOld c ν g →
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × Space => wardXr ν μ R c χy g x.1 x.2) ∧
      (∀ τ y, wardXr ν μ R c χy g (τ + 2 * c / R) y = wardXr ν μ R c χy g τ y) ∧
      (∀ τ y, ∑ j : Fin 3, physPd (wardXr ν μ R c χy g τ) j y j = 0) ∧
      ∀ τ, AxiNoSwirlPt (wardXr ν μ R c χy g τ)

/-- **(b2) The Ward fields of a smooth displacement are smooth** (source 4171-4173, 4276-4282;
pointwise calculus): for jointly `C^∞` background `U`, pressure `p` and displacement `X`, the
fields `h = [U, X]`, `Y = D_{μ+1}X`, `Ẽ_μ` and `X·∇p` are jointly `C^∞` on `ℝ × ℝ³`. -/
def WardFieldsSmooth : Prop :=
  ∀ (ν μ : ℝ) (U X : ℝ → Space → Space) (p : ℝ → Space → ℝ),
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × Space => U x.1 x.2) →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × Space => p x.1 x.2) →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × Space => X x.1 x.2) →
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun x : ℝ × Space => physBracket (U x.1) (X x.1) x.2) ∧
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun x : ℝ × Space => physDmu ν (μ + 1) X x.1 x.2) ∧
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun x : ℝ × Space => physResidual ν μ U p X x.1 x.2) ∧
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun x : ℝ × Space => ∑ j : Fin 3, X x.1 x.2 j * physGrad (p x.1) x.2 j)

/-- **(b3) The Ward operations preserve the symmetry** (source 121-124, 6314-6316: orthogonal maps
fixing the axis commute with the heat and Leray operators and the nonlinearity; 4139-4141 and
4171-4173, 4276-4282): for an exact profile `(U, p)` with `U` axisymmetric without swirl (so is
`∇p = -(D₀U + U·∇U)`, `IsExactProfile.equation`) and a smooth axisymmetric swirl-free `X`, the
fields `[U, X]`, `Ẽ_μ` and `D_{μ+1}X + [U, X]` are axisymmetric without swirl. -/
def WardFieldsAxi : Prop :=
  ∀ (ν μ P : ℝ) (U X : ℝ → Space → Space) (p : ℝ → Space → ℝ),
    IsExactProfile ν P U p → (∀ τ, AxiNoSwirlPt (U τ)) →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × Space => X x.1 x.2) →
    (∀ τ, AxiNoSwirlPt (X τ)) →
    ∀ τ, AxiNoSwirlPt (fun y => physBracket (U τ) (X τ) y) ∧
      AxiNoSwirlPt (physResidual ν μ U p X τ) ∧
      AxiNoSwirlPt (fun y => physDmu ν (μ + 1) X τ y + physBracket (U τ) (X τ) y)

/-- **(b4) Symmetric fields are lifts of their chart coefficients** (source 2666-2689, 121-124):
a `2c/R`-periodic field, axisymmetric without swirl and vanishing on the axis, is
`velPhys R c (coefOf R F)` everywhere (off the axis this is `velPhysCoefOf_of`; on the axis
`age R y = 0` in Lean, so both sides vanish). -/
def AxiLiftOfAxi : Prop :=
  ∀ (R c : ℝ) (F : ℝ → Space → Space), 0 < R → 0 < c →
    (∀ τ, AxiNoSwirlPt (F τ)) → (∀ τ y, F (τ + 2 * c / R) y = F τ y) →
    (∀ τ y, y ∈ axis → F τ y = 0) → IsAxiLift R c F

/-! ## 2. Proved here -/

/-- `χ_o` turns smooth chart data into smooth old data (source 4163-4166: `χ_o(s) = χ̂_o(νs)`
vanishes for `νs ≤ 6/5`). -/
theorem chiOSmoothRep {c mZ ρb γ ν : ℝ} {χo : ℝ → ℝ} (hχo : IsOutwardCutoff χo)
    (T : StrG c mZ ρb γ ν) {G₁ G₂ : Chart → Ten3}
    (h1 : (T.fst : Chart → Ten3) =ᵐ[gainZ1Measure c mZ γ ν] G₁)
    (h2 : (T.snd : Chart → Ten3) =ᵐ[gainHTMeasure c ρb γ ν] G₂)
    (hG1 : IsSmoothChart c G₁) (hG2 : IsSmoothChart c G₂) :
    ∃ g₁ g₂ : Chart → Ten3,
      ((chiOStr c mZ ρb γ ν hχo T).fst : Chart → Ten3) =ᵐ[gainZ1Measure c mZ γ ν] g₁ ∧
      ((chiOStr c mZ ρb γ ν hχo T).snd : Chart → Ten3) =ᵐ[gainHTMeasure c ρb γ ν] g₂ ∧
      IsSmoothOld c ν (g₁ + g₂) := by
  obtain ⟨a1, a2⟩ := chiOStrApply c mZ ρb γ ν χo hχo T
  have hcut : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (cutFun χo ν) := by
    unfold cutFun
    exact hχo.smooth.comp (contDiff_const.mul contDiff_fst)
  refine ⟨cutFun χo ν • G₁, cutFun χo ν • G₂, ?_, ?_, ⟨⟨?_, ?_, ?_⟩, ?_⟩⟩
  · filter_upwards [a1, h1] with q hq1 hq2
    rw [hq1, hq2]
    rfl
  · filter_upwards [a2, h2] with q hq1 hq2
    rw [hq1, hq2]
    rfl
  · exact (hcut.smul hG1.smooth).add (hcut.smul hG2.smooth)
  · exact hG1.compact.smul_left.add hG2.compact.smul_left
  · refine (tsupport_add _ _).trans (Set.union_subset ?_ ?_)
    · exact (tsupport_smul_subset_right (cutFun χo ν) G₁).trans hG1.inChart
    · exact (tsupport_smul_subset_right (cutFun χo ν) G₂).trans hG2.inChart
  · intro q hq
    simp [cutFun, hχo.zero _ hq]

section Zero

theorem physPd_zero_fun (j : Fin 3) (y : Space) : physPd (0 : Space → Space) j y = 0 := by
  simp [physPd]

theorem physPd2_zero_fun (j l : Fin 3) (y : Space) : physPd2 (0 : Space → Space) j l y = 0 := by
  unfold physPd2
  have h : (fun y' => physPd (0 : Space → Space) l y') = 0 :=
    funext fun y' => physPd_zero_fun l y'
  rw [h]
  exact physPd_zero_fun j y

theorem physLap_zero_fun (y : Space) : physLap (0 : Space → Space) y = 0 := by
  simp [physLap, physPd2_zero_fun]

/-- The Ward fields of a displacement vanishing on an open set vanish there (all operations are
local). -/
theorem physFields_eq_zero_of_nhds {ν μ : ℝ} {U X : ℝ → Space → Space} {p : ℝ → Space → ℝ}
    {s : Set Space} (hs : IsOpen s) (hX : ∀ τ, ∀ y ∈ s, X τ y = 0) (τ : ℝ) {y : Space}
    (hy : y ∈ s) :
    physBracket (U τ) (X τ) y = 0 ∧ physDmu ν (μ + 1) X τ y = 0 ∧
      physResidual ν μ U p X τ y = 0 := by
  have hev : ∀ (t : ℝ) {y' : Space}, y' ∈ s → X t =ᶠ[𝓝 y'] (0 : Space → Space) := by
    intro t y' hy'
    filter_upwards [hs.mem_nhds hy'] with z hz
    exact hX t z hz
  have hD : ∀ {y' : Space}, y' ∈ s → physDmu ν (μ + 1) X τ y' = 0 := by
    intro y' hy'
    rw [physDmu_congr_nhds (X₂ := fun _ => (0 : Space → Space)) (fun t => hev t hy') τ]
    simp [physDmu, physLap_zero_fun]
  refine ⟨?_, hD hy, ?_⟩
  · unfold physBracket
    rw [(hev τ hy).fderiv_eq, hX τ y hy]
    simp
  · have hDev : physDmu ν (μ + 1) X τ =ᶠ[𝓝 y] (0 : Space → Space) := by
      filter_upwards [hs.mem_nhds hy] with z hz
      exact hD hz
    unfold physResidual
    rw [hDev.fderiv_eq, physCdiff_congr_nhds _ (hev τ hy), physUUD2_congr_nhds _ (hev τ hy),
      physDXp_congr_nhds _ (hev τ hy)]
    simp [physCdiff, physUUD2, physDXp, physPd_zero_fun, physPd2_zero_fun]
    all_goals rfl

end Zero

/-- The Ward fields of periodic data are periodic. -/
theorem wardFields_periodic {ν μ P : ℝ} {U X : ℝ → Space → Space} {p : ℝ → Space → ℝ}
    (hU : ∀ τ y, U (τ + P) y = U τ y) (hp : ∀ τ y, p (τ + P) y = p τ y)
    (hX : ∀ τ y, X (τ + P) y = X τ y) (τ : ℝ) :
    (∀ y, physBracket (U (τ + P)) (X (τ + P)) y = physBracket (U τ) (X τ) y) ∧
      physDmu ν (μ + 1) X (τ + P) = physDmu ν (μ + 1) X τ ∧
      physResidual ν μ U p X (τ + P) = physResidual ν μ U p X τ := by
  have eU : U (τ + P) = U τ := funext (hU τ)
  have eX : X (τ + P) = X τ := funext (hX τ)
  have ep : p (τ + P) = p τ := funext (hp τ)
  have eD : ∀ μ' : ℝ, physDmu ν μ' X (τ + P) = physDmu ν μ' X τ := by
    intro μ'
    funext y
    have hper : deriv (fun t => X t y) (τ + P) = deriv (fun t => X t y) τ := by
      rw [← deriv_comp_add_const]
      congr 1
      funext t
      exact hX t y
    unfold physDmu
    rw [hper, eX]
  refine ⟨fun y => by rw [eU, eX], eD (μ + 1), ?_⟩
  funext y
  unfold physResidual
  rw [eD (μ + 1), eU, eX, ep]

section Assembly

variable {c mZ ρb γ ν : ℝ} {Aff : Type} [NormedAddCommGroup Aff] [NormedSpace ℝ Aff]
  [CompleteSpace Aff]

/-- Smooth old data give a `SmoothWardInput` (the leaves (b1)-(b4)). -/
theorem smoothWardInput_of {ν μ R c : ℝ} {χy : ℝ → ℝ} {U : ℝ → SpatialField}
    {p : ℝ → Space → ℝ} {g : Chart → Ten3} (hν : 0 < ν) (hR : 0 < R) (hc : 0 < c)
    (hμ : -(1 / 4) < μ) (hχy : IsYoungCutoff χy) (hUp : IsExactProfile ν (2 * c / R) U p)
    (hax : ∀ τ, AxiNoSwirlPt (U τ)) (hX : WardXrSmoothData) (hF : WardFieldsSmooth)
    (hA : WardFieldsAxi) (hL : AxiLiftOfAxi) (hg : IsSmoothOld c ν g) :
    SmoothWardInput ν μ R c χy U p g := by
  obtain ⟨sX, pX, dX, aX⟩ := hX ν μ R c χy hν hR hc hμ hχy g hg
  obtain ⟨sH, sY, sE, sQ⟩ := hF ν μ U (wardXr ν μ R c χy g) p hUp.smoothU hUp.smoothP sX
  set s : Set Space := {y : Space | ϱ y < R * Real.sqrt ν} with hs_def
  have hs : IsOpen s := isOpen_lt (by unfold ϱ; fun_prop) continuous_const
  have hz : ∀ τ, ∀ y ∈ s, wardXr ν μ R c χy g τ y = 0 := by
    intro τ y hy
    refine wardXr_eq_zero_of_sq_le hχy g τ ?_
    have h0 : 0 ≤ ϱ y := Real.sqrt_nonneg _
    have hy' : ϱ y < R * Real.sqrt ν := hy
    have hsq : (R * Real.sqrt ν) ^ 2 = ν * R ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hν.le]
      ring
    nlinarith
  have hax0 : ∀ y, y ∈ axis → y ∈ s := by
    intro y hy
    show ϱ y < R * Real.sqrt ν
    rw [(mem_axis_iff y).1 hy]
    positivity
  have hper := fun τ =>
    wardFields_periodic (ν := ν) (μ := μ) hUp.periodicU hUp.periodicP pX τ
  have hzero := fun τ y (hy : y ∈ axis) =>
    physFields_eq_zero_of_nhds (ν := ν) (μ := μ) (U := U) (p := p) hs hz τ (hax0 y hy)
  have hAx := hA ν μ (2 * c / R) U (wardXr ν μ R c χy g) p hUp hax sX aX
  have pH : ∀ τ y, wardHr ν μ R c χy U g (τ + 2 * c / R) y = wardHr ν μ R c χy U g τ y :=
    fun τ y => (hper τ).1 y
  have pY : ∀ τ y, wardYr ν μ R c χy g (τ + 2 * c / R) y = wardYr ν μ R c χy g τ y :=
    fun τ y => congrFun (hper τ).2.1 y
  have pE : ∀ τ y, wardEr ν μ R c χy U p g (τ + 2 * c / R) y = wardEr ν μ R c χy U p g τ y :=
    fun τ y => congrFun (hper τ).2.2 y
  have zH : ∀ τ y, y ∈ axis → wardHr ν μ R c χy U g τ y = 0 := fun τ y hy => (hzero τ y hy).1
  have zY : ∀ τ y, y ∈ axis → wardYr ν μ R c χy g τ y = 0 := fun τ y hy => (hzero τ y hy).2.1
  have zE : ∀ τ y, y ∈ axis → wardEr ν μ R c χy U p g τ y = 0 :=
    fun τ y hy => (hzero τ y hy).2.2
  exact
    { oldData := hg
      smoothX := sX
      periodicX := pX
      solenoidalX := dX
      smoothH := sH
      smoothY := sY
      smoothE := sE
      smoothQ := sQ
      periodicH := pH
      periodicY := pY
      periodicE := pE
      liftH := hL R c _ hR hc (fun τ => (hAx τ).1) pH zH
      liftE := hL R c _ hR hc (fun τ => (hAx τ).2.1) pE zE
      liftYH := hL R c _ hR hc (fun τ => (hAx τ).2.2)
        (fun τ y => by simp only [pY τ y, pH τ y])
        (fun τ y hy => by simp only [zY τ y hy, zH τ y hy, add_zero]) }

/-- **`WardSmoothDense` from the leaves** (source 4284-4286): the smooth class contains the dense
set of `StrSmoothDense`. -/
theorem wardSmoothDense_of (B : ReturnBase c mZ ρb γ ν Aff) {ε μ : ℝ} {χo : ℝ → ℝ}
    (hχo : IsOutwardCutoff χo) (χy : ℝ → ℝ) (hχy : IsYoungCutoff χy)
    {U : ℝ → SpatialField} {p : ℝ → Space → ℝ} (hc : 0 < c) (hν : 0 < ν) (hε : 0 < ε)
    (hμ : -(1 / 4) < μ) (hUp : IsExactProfile ν (2 * ε * c) U p)
    (hax : ∀ τ, AxiNoSwirlPt (U τ))
    (hD : StrSmoothDense c mZ ρb γ ν) (hX : WardXrSmoothData) (hF : WardFieldsSmooth)
    (hA : WardFieldsAxi) (hL : AxiLiftOfAxi) :
    WardSmoothDense B ε μ hχo χy U p := by
  have hP : (2 * c / ε⁻¹ : ℝ) = 2 * ε * c := by
    rw [div_inv_eq_mul]
    ring
  have hUp' : IsExactProfile ν (2 * c / ε⁻¹) U p := by
    rw [hP]
    exact hUp
  refine Dense.mono ?_ (hD hc hν)
  rintro T ⟨G₁, G₂, h1, h2, hG1, hG2⟩
  obtain ⟨g₁, g₂, e1, e2, hold⟩ := chiOSmoothRep hχo T h1 h2 hG1 hG2
  exact ⟨g₁, g₂, e1, e2,
    smoothWardInput_of hν (inv_pos.2 hε) hc hμ hχy hUp' hax hX hF hA hL hold⟩

end Assembly

end UnforcedLeray.Short.PartIIIb.Concrete
