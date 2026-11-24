import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Ward.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Background.Levels
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_1.L5
import UnforcedLeray.Analysis.LerayProjection.Basic

/-!
# The pressure gradient of the exact background in `Y₂` on the young support (source 117-118,
2505-2524, 2607-2612, 2641-2642, 2671-2689, 4138-4145, 5245-5260)

Source of record: `the November 2 reference manuscript` (73 pages).

Task `PartIII-b:C/ward/13/org`.  `BgPresY2` (`Ward/Bg/Defs.lean`) asks, at the levels of the
regime and for every exact split whose sum is an exact profile, that the chart coefficient
`s^{-1/2}∇p` read at azimuth `0` and restricted to the young chart region `νs ≤ 1` be in
`L²(srcMeasure c)` (lift identity 2684-2689: this is `R⁻¹‖1_{young}∇p‖_{Y₂}`).

## Why the ball datum

The chart integral reads `∇p` on the half-plane `φ = 0` only.  It is the `Y₂` norm of `∇p` only
because `U`, hence `|∇p|`, is axisymmetric (the azimuthal integration of 2688-2689), and the
`L²` bound of `∇p` comes from `D^jU ∈ C_per L⁴` (2607-2612).  Both are facts about *the*
background of `short-bg:result`: the fixed point of the contraction on the ball
`‖z‖_Z ≤ 𝒫_ν e^{m/ν} ε^{3/11}`, `2m < 3d₋/11` (2505-2524), whose symmetry and regularity
`short-bg:strong` gives (2522-2562, `IIb.StrongRegularity`, stated on the ball).  `IIb.ExactSplitII`
does not bound `‖z‖_Z` (see `Background/Ball.lean`), so for a split that is only `ExactSplitII`
neither fact is available, and the half-plane integral of a non-symmetric field is not controlled
by its `L²(ℝ³)` norm.  `BgPresY2B` below is `BgPresY2` at the levels of the contraction-ball
background (`AtBallLevels`, with the quantifiers of `BgAxiLevels`); the actual levels carry the
ball datum (`SeqData.IsActualLevel.ball`).

## The argument (`presY2_of_level`, `bgPresY2B_of`)

1. `s · |s^{-1/2}∇p|² = |∇p|²` moves `srcMeasure c = π s^{-3/2}dς` to `s^{-5/2}dς`;
2. `ChartPhaseLIntegral` (2684-2689, proved): `∫_0^P ∫ F(chartOf R c z τ) dz dτ = P πR² ∫ F
   d(s^{-5/2}dς)`, `P = 2c/R`;
3. off the axis, `chartTau R (chartOf R c z τ) = τ - kP` (`ChartTauOf`) and
   `chartY R (chartOf R c z τ) = (ϱ(z), 0, z₃)` (`ChartYOf`); the pressure is `P`-periodic
   (`IsExactProfile.periodicP`), and `(ϱ(z), 0, z₃) = g z` for an isometry `g` fixing `e₃`
   (`AzimuthRot`) with `∇p(τ, gz) = g∇p(τ, z)` (`PresGradEquivar`, from the profile equation
   4138-4141 and the symmetry of `U`, 2522-2523, 4144-4145, `BgAxiLevels`);
4. `∇p(τ) = -(I - 𝐏)(U·∇U)(τ)` (`BgPresLeray`: the global pressure `p = Σ R_iR_k(U_iU_k)` of
   117-118, 2641-2642, as `∇p_V = -(I-𝐏)(V·∇V)` in 5245-5246), so
   `‖∇p(τ)‖₂ ≤ ‖U·∇U(τ)‖₂ ≤ ‖DU(τ)‖₄‖U(τ)‖₄` (`LerayComplNormLe`, `ProdL2OfL4`), uniformly in `τ`
   by `D^jU ∈ C_per L⁴` (`BgUL4`, 2607-2612).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (Params)

/-! ## 1. The levels of the contraction-ball background -/

/-- **A property of the exact background at the levels of the contraction ball** (source
2505-2524 `short-bg:result`, 2706-2711, 4138-4145): for the slow age `Σ > 0`, the growing
eigenpair `(λ, q)`, `0 < m` with `2m < 3d₋/11` (the contraction condition, 2510-2512) and the
ball constants `C₁ > 0, k₁`, there is `ν₀ > 0` such that at every level of the regime with
`ν ≤ ν₀`, `Σ = p.ageCut`, `q = p.mode`, every split `(V, r_b)` which is the contraction-ball
background of radius `C₁ν^{-k₁}e^{m/ν}ε^{3/11}` (`IsBallSplit`) and whose sum `U = V + r_b` is an
exact profile with pressure `p` (`IsExactProfile`, period `P = 2εc`) has `Φ`.  The quantifiers
are those of `BgAxiLevels` (`Background/Levels.lean`). -/
def AtBallLevels
    (Φ : Params → (ℝ → SpatialField) → (ℝ → SpatialField) → (ℝ → Space → ℝ) → Prop) : Prop :=
  ∀ (Sig : ℝ) (lam : ℂ) (q : UnforcedLeray.Blueprint.Planar.Profile), 0 < Sig →
    UnforcedLeray.Blueprint.Planar.IsGrowingEigenpair lam q →
  ∀ m : ℝ, 0 < m → ∀ dm dp : ℝ, 0 < dm → 2 * m < 3 * dm / 11 →
  ∀ (C₁ : ℝ) (k₁ : ℕ), 0 < C₁ →
    ∃ ν₀ : ℝ, 0 < ν₀ ∧
      ∀ (p : Params) (d : ℝ), UnforcedLeray.Short.IIb.BgRegime p d dm dp → p.ν ≤ ν₀ →
      p.ageCut = Sig → p.mode = q →
      ∀ (V rb : ℝ → SpatialField) (pres : ℝ → Space → ℝ),
        IsBallSplit p (UnforcedLeray.Short.IIb.rhoB p m C₁ k₁) V rb →
        IsExactProfile p.ν p.period (fun τ y => V τ y + rb τ y) pres → Φ p V rb pres

theorem AtBallLevels.and
    {Φ Ψ : Params → (ℝ → SpatialField) → (ℝ → SpatialField) → (ℝ → Space → ℝ) → Prop}
    (h1 : AtBallLevels Φ) (h2 : AtBallLevels Ψ) :
    AtBallLevels fun p V rb pres => Φ p V rb pres ∧ Ψ p V rb pres := by
  intro Sig lam q hSig hq m hm dm dp hdm h2m C₁ k₁ hC₁
  obtain ⟨ν₁, hν₁, H1⟩ := h1 Sig lam q hSig hq m hm dm dp hdm h2m C₁ k₁ hC₁
  obtain ⟨ν₂, hν₂, H2⟩ := h2 Sig lam q hSig hq m hm dm dp hdm h2m C₁ k₁ hC₁
  refine ⟨min ν₁ ν₂, lt_min hν₁ hν₂, fun p d hreg hν hS hq' V rb pres hb hU => ⟨?_, ?_⟩⟩
  · exact H1 p d hreg (hν.trans (min_le_left _ _)) hS hq' V rb pres hb hU
  · exact H2 p d hreg (hν.trans (min_le_right _ _)) hS hq' V rb pres hb hU

theorem AtBallLevels.mono'
    {Φ Ψ : Params → (ℝ → SpatialField) → (ℝ → SpatialField) → (ℝ → Space → ℝ) → Prop}
    (h : AtBallLevels Φ)
    (hΦ : ∀ (p : Params) (V rb : ℝ → SpatialField) (pres : ℝ → Space → ℝ),
      IsExactProfile p.ν p.period (fun τ y => V τ y + rb τ y) pres →
        Φ p V rb pres → Ψ p V rb pres) :
    AtBallLevels Ψ := by
  intro Sig lam q hSig hq m hm dm dp hdm h2m C₁ k₁ hC₁
  obtain ⟨ν₀, hν₀, H⟩ := h Sig lam q hSig hq m hm dm dp hdm h2m C₁ k₁ hC₁
  exact ⟨ν₀, hν₀, fun p d hreg hν hS hq' V rb pres hb hU =>
    hΦ p V rb pres hU (H p d hreg hν hS hq' V rb pres hb hU)⟩

/-- The symmetry of the ball background (`BgAxiLevels`, from `short-bg:strong`) in the form of
`AtBallLevels`. -/
theorem atBallLevels_axi (hA : BgAxiLevels) :
    AtBallLevels fun _ V rb _ => ∀ τ : ℝ, AxiNoSwirlPt (fun y => V τ y + rb τ y) := by
  intro Sig lam q hSig hq m hm dm dp hdm h2m C₁ k₁ hC₁
  obtain ⟨ν₀, hν₀, H⟩ := hA Sig lam q hSig hq m hm dm dp hdm h2m C₁ k₁ hC₁
  exact ⟨ν₀, hν₀, fun p d hreg hν hS hq' V rb _ hb _ τ => H p d hreg hν hS hq' V rb hb τ⟩

/-! ## 2. The target at the ball levels -/

/-- **`BgPresY2` at the levels of the contraction-ball background** (source 2607-2612, 2641-2642,
5245-5260, lift identity 2684-2689; the ball 2505-2524): for the exact background `U = V + r_b`
of `short-bg:result` and its pressure, the chart coefficient `s^{-1/2}∇p` read at
`(chartTau R x, chartY R x)` (azimuth `0`) and restricted to the young chart region `νs ≤ 1` has
finite `L²(srcMeasure c)` norm (`R⁻¹‖1_{young}∇p‖_{Y₂} < ∞`). -/
def BgPresY2B : Prop :=
  AtBallLevels fun p _ _ pres =>
    eLpNorm ({x : Chart | p.ν * x.1 ≤ 1}.indicator fun x : Chart =>
        (Real.sqrt x.1)⁻¹ • physGrad (pres (NearInst.chartTau p.R x)) (NearInst.chartY p.R x))
      2 (srcMeasure p.c) < ⊤

/-! ## 3. Leaves -/

/-- **The phase of the chart point of `(z, τ)`** (source 2671-2675: `s = R²/ϱ²`,
`q = R log(ϱ/R) + Rτ/2` reduced to the cell, `η = Rz₃/ϱ`; `chartTau` inverts it up to the
period): `chartTau R (chartOf R c z τ) = τ - k·(2c/R)` with `k` the cell index of the reduction.
On the axis both logarithms are `log 0 = 0` and the identity persists. -/
def ChartTauOf : Prop :=
  ∀ (R c : ℝ) (z : Space) (τ : ℝ), R ≠ 0 →
    NearInst.chartTau R (NearInst.chartOf R c z τ) =
      τ - ((⌊(R * Real.log (NearInst.hRad z / R) + R * τ / 2) / c + 1 / 2⌋ : ℤ) : ℝ) *
        (2 * c / R)

/-- **The similarity point of the chart point of `z`** (source 2671-2675): off the axis,
`chartY R (chartOf R c z τ) = (ϱ(z), 0, z₃)`, the point of the half-plane `φ = 0` on the circle of
`z` about the axis (`√s = R/ϱ`, `R/√s = ϱ`, `η/√s = z₃`). -/
def ChartYOf : Prop :=
  ∀ (R c : ℝ) (z : Space) (τ : ℝ), 0 < R → 0 < NearInst.hRad z →
    NearInst.chartY R (NearInst.chartOf R c z τ) =
      WithLp.toLp 2 ![NearInst.hRad z, 0, z 2]

/-- **Rotation to the half-plane `φ = 0`** (source 117-121, 2688-2689 "after azimuthal
integration"): every `z` is carried to `(ϱ(z), 0, z₃)` by a linear isometry fixing `e₃` (a rotation
about the axis; the identity on the axis). -/
def AzimuthRot : Prop :=
  ∀ z : Space, ∃ g : Space ≃ₗᵢ[ℝ] Space, UnforcedLeray.FixesAxis g ∧
    g z = WithLp.toLp 2 ![NearInst.hRad z, 0, z 2]

/-- **The Laplacian commutes with isometries** (used for the term `νΔU` of the profile equation,
4138-4141): if `f(gy) = g f(y)` for a linear isometry `g` and `f ∈ C²`, then
`Δf(gy) = g Δf(y)`. -/
def PhysLapEquivar : Prop :=
  ∀ (f : Space → Space) (g : Space ≃ₗᵢ[ℝ] Space), ContDiff ℝ 2 f →
    (∀ y, f (g y) = g (f y)) → ∀ y, physLap f (g y) = g (physLap f y)

/-- **The pressure gradient of a symmetric exact profile is equivariant** (source 4138-4145: the
profile equation `D₀U + U·∇U + ∇p = 0` fixes `∇p` pointwise, and `U` has "the prescribed
orthogonal symmetry"; 117-121): if `U(τ)` is axisymmetric without swirl at every phase, then
`∇p(τ, gy) = g∇p(τ, y)` for every isometry `g` fixing `e₃`. -/
def PresGradEquivar : Prop :=
  ∀ (ν P : ℝ) (U : ℝ → SpatialField) (pres : ℝ → Space → ℝ), IsExactProfile ν P U pres →
    (∀ τ, AxiNoSwirlPt (U τ)) → ∀ g : Space ≃ₗᵢ[ℝ] Space, UnforcedLeray.FixesAxis g →
      ∀ (τ : ℝ) (y : Space), physGrad (pres τ) (g y) = g (physGrad (pres τ) y)

/-- **The pressure gradient of an exact profile is jointly continuous** (source 4138-4141: the
pressure is smooth on `ℝ × ℝ³`, `IsExactProfile.smoothP`). -/
def PresGradCont : Prop :=
  ∀ (ν P : ℝ) (U : ℝ → SpatialField) (pres : ℝ → Space → ℝ), IsExactProfile ν P U pres →
    Continuous fun x : ℝ × Space => physGrad (pres x.1) x.2

/-- **`D^jU ∈ C_per L⁴` for `j ≤ 1`** (source 2607-2612: "The inverse-distance bounds and the
all-age expansion give `D^jV ∈ C_per L⁴`. For `w`, interpolation between its `C_per L^p`
derivatives and their uniform supremum bounds gives `D^jw ∈ C_per L⁴`. Therefore `D^jU ∈ C_per L⁴`
for `j ≤ 2`"; the background is that of `short-bg:result`, 2505-2524): at the ball levels,
`U(τ) = V(τ) + r_b(τ)` and its derivative are bounded in `L⁴(ℝ³)` uniformly in the phase. -/
def BgUL4 : Prop :=
  AtBallLevels fun _ V rb _ => ∃ C : ℝ, ∀ τ : ℝ,
    eLpNorm (fun y => V τ y + rb τ y) 4 volume ≤ ENNReal.ofReal C ∧
      eLpNorm (fun y => fderiv ℝ (fun y' => V τ y' + rb τ y') y) 4 volume ≤ ENNReal.ofReal C

/-- **The pressure of the exact background is the Riesz pressure** (source 117-118: "The pressure
is the global choice `p = Σ R_iR_k(u_iu_k)`"; 2521-2523: the projected equation
`A₀U + 𝐏(U·∇U) = 0`; 2641-2642: "`p_U = Σ R_iR_j(U_iU_j) ∈ C_per L²` recovers the discarded
gradient part of the exact projected equation"; 4138-4141: the profile equation fixes `∇p`
pointwise; 5245-5246, the same formula `∇p_V = -(I - 𝐏)(V·∇V)` for `V`): at the ball levels, at
every phase with `U·∇U ∈ L²`, `∇p = -(I - 𝐏)(U·∇U)` a.e., `𝐏` the `L²` Leray projection. -/
def BgPresLeray : Prop :=
  AtBallLevels fun _ V rb pres => ∀ τ : ℝ,
    MemLp (fun y => fderiv ℝ (fun y' => V τ y' + rb τ y') y (V τ y + rb τ y)) 2 volume →
      physGrad (pres τ) =ᵐ[volume]
        ⇑(-(UnforcedLeray.toL2
              (fun y => fderiv ℝ (fun y' => V τ y' + rb τ y') y (V τ y + rb τ y)) -
            UnforcedLeray.Leray.projection (UnforcedLeray.toL2
              (fun y => fderiv ℝ (fun y' => V τ y' + rb τ y') y (V τ y + rb τ y)))))

/-- **Hölder for `U·∇U`** (source 5246 `‖∇p_V‖₂ ≤ C‖V‖_∞‖DV‖₂` in its `L⁴ × L⁴` form, with
2607-2612): for `f ∈ C¹` with `‖f‖₄, ‖Df‖₄ ≤ C`, `f·∇f = Df(f)` is in `L²` with
`‖Df(f)‖₂ ≤ C²`. -/
def ProdL2OfL4 : Prop :=
  ∀ (f : Space → Space) (C : ℝ), ContDiff ℝ 1 f →
    eLpNorm f 4 volume ≤ ENNReal.ofReal C →
    eLpNorm (fun y => fderiv ℝ f y) 4 volume ≤ ENNReal.ofReal C →
      MemLp (fun y => fderiv ℝ f y (f y)) 2 volume ∧
        eLpNorm (fun y => fderiv ℝ f y (f y)) 2 volume ≤ ENNReal.ofReal (C * C)

/-- **`I - 𝐏` is a contraction on `L²`** (source 5246-5247: `‖∇p_V‖₂ ≤ C‖V‖_∞‖DV‖₂`; `𝐏` is the
orthogonal projection onto the solenoidal fields, `Leray.projection`). -/
def LerayComplNormLe : Prop :=
  ∀ F : L2Space, ‖F - UnforcedLeray.Leray.projection F‖ ≤ ‖F‖

/-! ## 4. Assembly -/

private theorem bgp_measurable_chartTau (R : ℝ) : Measurable (NearInst.chartTau R) := by
  unfold NearInst.chartTau
  fun_prop

private theorem bgp_measurable_chartY (R : ℝ) : Measurable (NearInst.chartY R) := by
  unfold NearInst.chartY
  have : Measurable fun p : Chart =>
      (![R / Real.sqrt p.1, 0, p.2.2 / Real.sqrt p.1] : Fin 3 → ℝ) := by
    refine measurable_pi_lambda _ fun i => ?_
    fin_cases i <;> simp <;> fun_prop
  exact (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).measurable.comp this

/-- Raising the age exponent by one multiplies the density by `s`. -/
private theorem bgp_lintegral_ageμ_succ {c : ℝ} (hc : 0 < c) (a : ℝ)
    {f : ℝ × (ℝ × ℝ) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ p, f p ∂ageμ c (a + 1) = ∫⁻ p, ENNReal.ofReal p.1 * f p ∂ageμ c a := by
  have hm : Measurable fun p : ℝ × (ℝ × ℝ) => ENNReal.ofReal p.1 * f p :=
    (ENNReal.measurable_ofReal.comp measurable_fst).mul hf
  rw [lintegral_ageμ hc _ hf, lintegral_ageμ hc _ hm]
  refine setLIntegral_congr_fun
    (measurableSet_Ioi.prod (measurableSet_Ico.prod MeasurableSet.univ)) fun p hp => ?_
  have hs : 0 < p.1 := hp.1
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  rw [Real.rpow_add hs, Real.rpow_one]
  ring

private theorem bgp_weight (s : ℝ) (v : Space) :
    ENNReal.ofReal s * ‖(Real.sqrt s)⁻¹ • v‖ₑ ^ 2 ≤ ‖v‖ₑ ^ 2 := by
  rcases le_or_gt s 0 with hs | hs
  · rw [ENNReal.ofReal_of_nonpos hs, zero_mul]
    exact zero_le
  · rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
      ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_mul hs.le]
    refine le_of_eq (congrArg ENNReal.ofReal ?_)
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, inv_pow, Real.sq_sqrt hs.le]
    field_simp

/-- **`BgPresY2` at one level** (source 2684-2689, 4138-4145): for a `P`-periodic exact profile
(`P = 2c/R`) with symmetric velocity and `‖∇p(τ)‖_{L²(ℝ³)} ≤ K < ∞` at every phase, the young
chart coefficient of `∇p` is in `L²(srcMeasure c)`. -/
theorem presY2_of_level (hT : ChartTauOf) (hYo : ChartYOf) (hrot : AzimuthRot)
    (hE : PresGradEquivar) (hC : PresGradCont)
    {ν R c P : ℝ} {U : ℝ → SpatialField} {pres : ℝ → Space → ℝ}
    (hR : 0 < R) (hc : 0 < c) (hP : P = 2 * c / R) (hU : IsExactProfile ν P U pres)
    (hax : ∀ τ, AxiNoSwirlPt (U τ)) {K : ℝ≥0∞} (hK : K < ⊤)
    (hL2 : ∀ τ, eLpNorm (physGrad (pres τ)) 2 volume ≤ K) (ν' : ℝ) :
    eLpNorm ({x : Chart | ν' * x.1 ≤ 1}.indicator fun x : Chart =>
        (Real.sqrt x.1)⁻¹ • physGrad (pres (NearInst.chartTau R x)) (NearInst.chartY R x))
      2 (srcMeasure c) < ⊤ := by
  set G : Chart → Space := fun x =>
    physGrad (pres (NearInst.chartTau R x)) (NearInst.chartY R x) with hG
  set S : Set Chart := {x : Chart | ν' * x.1 ≤ 1} with hS
  set H : Chart → ℝ≥0∞ := S.indicator fun x => ‖G x‖ₑ ^ 2 with hH
  have hGm : Measurable G := (hC ν P U pres hU).measurable.comp
    ((bgp_measurable_chartTau R).prodMk (bgp_measurable_chartY R))
  have hSm : MeasurableSet S :=
    measurableSet_le (measurable_const.mul measurable_fst) measurable_const
  have hHm : Measurable H := (hGm.enorm.pow_const 2).indicator hSm
  have hFm : Measurable fun x : Chart => (Real.sqrt x.1)⁻¹ • G x :=
    ((Real.continuous_sqrt.measurable.comp measurable_fst).inv).smul hGm
  -- the `L²` norm as a lintegral
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  rw [srcMeasure, lintegral_smul_measure]
  refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
  -- step 1: the weight `s^{-3/2}` to `s^{-5/2}`
  have hstep : ∫⁻ x, ‖S.indicator (fun x : Chart => (Real.sqrt x.1)⁻¹ • G x) x‖ₑ ^ 2
      ∂ageμ c (-3 / 2) ≤ ∫⁻ x, H x ∂ageμ c (-5 / 2) := by
    rw [show (-3 / 2 : ℝ) = -5 / 2 + 1 by norm_num,
      bgp_lintegral_ageμ_succ hc _ ((hFm.indicator hSm).enorm.pow_const 2)]
    refine lintegral_mono fun x => ?_
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx, hH, Set.indicator_of_mem hx]
      exact bgp_weight x.1 (G x)
    · rw [Set.indicator_of_notMem hx, enorm_zero, zero_pow two_ne_zero, mul_zero]
      exact zero_le
  refine lt_of_le_of_lt hstep ?_
  -- step 2: the chart phase integral
  have hCP := chartPhaseLIntegral R c hR hc H hHm
  have hper : Function.Periodic pres P := fun τ => funext fun y => hU.periodicP τ y
  -- step 3: at each phase, the chart integral is the `L²(ℝ³)` norm
  have hpt : ∀ τ, ∀ z : Space, z ∉ axis →
      H (NearInst.chartOf R c z τ) ≤ ‖physGrad (pres τ) z‖ₑ ^ 2 := by
    intro τ z hz
    have hρ : 0 < NearInst.hRad z := by
      have h1 : ϱ z ≠ 0 := fun h => hz ((mem_axis_iff z).2 h)
      exact lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm h1)
    refine (Set.indicator_le_self S (fun x => ‖G x‖ₑ ^ 2) _).trans (le_of_eq ?_)
    show ‖physGrad (pres (NearInst.chartTau R (NearInst.chartOf R c z τ)))
        (NearInst.chartY R (NearInst.chartOf R c z τ))‖ₑ ^ 2 = _
    rw [hT R c z τ hR.ne', hYo R c z τ hR hρ, ← hP, hper.sub_int_mul_eq]
    obtain ⟨g, hg, hgz⟩ := hrot z
    rw [← hgz, hE ν P U pres hU hax g hg τ z, ← ofReal_norm, ← ofReal_norm,
      LinearIsometryEquiv.norm_map]
  have hτ : ∀ τ, ∫⁻ z, H (NearInst.chartOf R c z τ) ≤ K ^ 2 := by
    intro τ
    refine (lintegral_mono_ae (ae_not_mem_axis.mono fun z hz => hpt τ z hz)).trans ?_
    have e := eLpNorm_nnreal_pow_eq_lintegral (f := physGrad (pres τ)) (μ := volume)
      (p := 2) two_ne_zero
    simp only [ENNReal.coe_ofNat, NNReal.coe_ofNat, ENNReal.rpow_two] at e
    rw [← e]
    exact pow_le_pow_left₀ zero_le (hL2 τ) 2
  have hLHS : ∫⁻ τ in Ioc 0 (2 * c / R), ∫⁻ z, H (NearInst.chartOf R c z τ) < ⊤ := by
    refine lt_of_le_of_lt (lintegral_mono fun τ => hτ τ) ?_
    rw [setLIntegral_const]
    exact ENNReal.mul_lt_top (ENNReal.pow_lt_top hK) (by simp)
  rw [hCP] at hLHS
  have h0 : ENNReal.ofReal (2 * c / R) * ENNReal.ofReal (Real.pi * R ^ 2) ≠ 0 := by
    refine mul_ne_zero ?_ ?_
    · exact (ENNReal.ofReal_pos.2 (by positivity)).ne'
    · exact (ENNReal.ofReal_pos.2 (by positivity)).ne'
  rcases ENNReal.mul_lt_top_iff.1 hLHS with h | h | h
  · exact h.2
  · exact absurd h h0
  · rw [h]
    exact ENNReal.zero_lt_top

/-- **`BgPresY2B`** from the leaves (source 2505-2524, 2607-2612, 2641-2642, 2684-2689,
4138-4145, 5245-5247). -/
theorem bgPresY2B_of (hT : ChartTauOf) (hYo : ChartYOf) (hrot : AzimuthRot)
    (hE : PresGradEquivar) (hC : PresGradCont) (hA : BgAxiLevels) (hL4 : BgUL4)
    (hLer : BgPresLeray) (hH : ProdL2OfL4) (hN : LerayComplNormLe) : BgPresY2B := by
  refine (((atBallLevels_axi hA).and hL4).and hLer).mono' ?_
  rintro p V rb pres hU ⟨⟨hax, C, hC4⟩, hLe⟩
  have hL2 : ∀ τ, eLpNorm (physGrad (pres τ)) 2 volume ≤ ENNReal.ofReal (C * C) := by
    intro τ
    have hWs : ContDiff ℝ 1 (fun y => V τ y + rb τ y) := by
      have h1 := hU.smoothU.comp (contDiff_prodMk_right (𝕜 := ℝ) (E := ℝ) (F := Space) τ)
      exact h1.of_le (by exact_mod_cast le_top)
    obtain ⟨hmem, hbd⟩ := hH (fun y => V τ y + rb τ y) C hWs (hC4 τ).1 (hC4 τ).2
    set F : Space → Space := fun y => fderiv ℝ (fun y' => V τ y' + rb τ y') y (V τ y + rb τ y)
      with hF
    rw [eLpNorm_congr_ae (hLe τ hmem), ← Lp.enorm_def, enorm_neg, ← ofReal_norm]
    refine ENNReal.ofReal_le_ofReal ((hN _).trans ?_)
    have htL : UnforcedLeray.toL2 F = hmem.toLp F := by
      unfold UnforcedLeray.toL2
      rw [dif_pos hmem]
    rw [htL, Lp.norm_toLp]
    exact ENNReal.toReal_le_of_le_ofReal (mul_self_nonneg C) hbd
  exact presY2_of_level hT hYo hrot hE hC p.R_pos p.c_pos p.period_eq hU hax
    ENNReal.ofReal_lt_top hL2 p.ν

end UnforcedLeray.Short.PartIIIb.Concrete
