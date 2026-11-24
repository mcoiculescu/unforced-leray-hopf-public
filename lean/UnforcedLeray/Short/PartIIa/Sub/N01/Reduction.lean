import UnforcedLeray.Short.PartIIa.Sub.N01.Defs
import UnforcedLeray.Short.PartIIa.ComposeFree
import UnforcedLeray.Short.PartIIa.Tasks.F01BodyResolvent
import UnforcedLeray.Short.PartIIa.Tasks.F02BodyResolventEquation
import UnforcedLeray.Short.PartIIa.Tasks.F04MaximalDomain
import UnforcedLeray.Short.PartIIa.Tasks.F06GraphBound
import UnforcedLeray.Short.PartIIa.Tasks.F12aSmoothSymSubmodule
import UnforcedLeray.Short.PartIIa.Tasks.F14WeakStressExists
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Proofs.ChartConjSmooth
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.TensorTestDivMem

/-!
# `PartII-a:N01` (design): assembly of `NearStressMapExists` from the leaves

Source of record: `the November 2 reference manuscript`,
lines 1638-1690 (`near:free-energy`, 1675-1683; the flat equation, 1684-1689), 1339-1372
(`bg:common-body-graph` and its semigroup inverse), 1546-1567 (`free:weak-stress`,
`free:stress-energy`), 1625-1632 (the transported stress map `J_v⁻¹ S_μ J_T`).

* `phaseLift_physRes` : `U ∘ (μ - A)⁻¹ = R_μ ∘ U` (Laplace integral of `PhaseSemigroupConj`).
* `bodyResolvent_bodyOp` : `R_μ g ∈ D₂` and `(μ + L) R_μ g = g` (the argument of `PartII-a:F07`).
* `phaseLift_liftVec_Teps` : for a real smooth tensor test `m` and `G = s div_ε m`,
  `U J_ε T_ε G = (2π)^{-1/2}√(Pε) S_μ(𝒩_T m)` — the transported stress map of 1627-1632 on smooth
  tests (`chartConjSmooth`, `PhaseLerayConj`, `PhaseDivScale`, injectivity of `μ + L` at `r = 2`).
* `norm_Teps_real_le`, `epsSmoothBound_of` : `‖T_ε(s div_ε M)‖_H ≤ 2((Re μ + 1/4)ν)^{-1/2}‖M‖_{H_T}`
  on smooth tests (`free:stress-energy`, `CartLiftNorm`, `TensorTestReIm`).
* `nearStressMapExists_of` : completion (`StressCompletion`) of the `ε > 0` and the flat bounds,
  with `((Re μ + 1/4)ν)^{-1/2} ≤ (1 + M + γ_*⁻¹) ν^{-1/2}`.
* `nearStressMapExists_of_parts` : the target from the eight leaf Props of `Sub/N01/Defs.lean` and
  `FlatSmoothBound` (`Sub/N01/FlatReduction.lean`; all eleven leaves: `Sub/N01/Assembly.lean`).

Correspondence with the design task's names: `BridgeRepsVec` is `phaseLift_liftVec_Teps` (with
`PhaseSemigroupConj`, `PhaseLerayConj`, and `B0223.J_RepsVec` inside `chartConjSmooth`);
`StressMapFromFree` is `EpsSmoothBound` + `StressCompletion`; `FlatStressMap` is
`FlatSmoothBound` + `StressCompletion`; the dissipation part is `DissipationBound` (task `N01/10`).
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

/-! ## The free resolvent in phase variables -/

/-- **`U ∘ (μ - A)⁻¹ = R_μ ∘ U`** (lines 1363-1372): the Laplace integral of the outer semigroup,
lifted by `U`, is the Laplace integral of the free semigroup `𝒯(t)` of `Y₂`. -/
theorem phaseLift_physRes (hS : PhaseSemigroupConj) {ν ε P : ℝ} [Fact (0 < P)] (hν : 0 < ν)
    (hε : 0 < ε) {U : B0223.X SpaceC P →ₗᵢ[ℂ] Yq P 2} (hU : IsPhaseLift ε P U) {μ : ℂ}
    (hγ : 0 < μ.re + 1 / 4) (Rm : Yq P 2 →L[ℂ] Yq P 2) (hq : (2 : ℝ≥0∞) ≠ ⊤)
    (hRm : ∀ f, Rm f = ∫ t in Set.Ioi (0 : ℝ),
      Complex.exp (-(μ * t)) • B0421.phaseT (P := P) (q := 2) hq ν t f)
    (F : B0223.X SpaceC P) :
    U (B0223.physRes (E := SpaceC) (P := P) hν ε μ F) = Rm (U F) := by
  have hω := B0223.omega_lt (E := SpaceC) (P := P) hγ hν ε
  rw [hRm, B0223.physRes, Infra.ExpSemigroup.laplace_apply' _ hω]
  have hint := (B0223.outerS (E := SpaceC) (P := P) hν ε).integrableOn_lapInt hω F
  have hcomm := U.toContinuousLinearMap.integral_comp_comm hint
  simp only [LinearIsometry.coe_toContinuousLinearMap] at hcomm
  refine Eq.trans hcomm.symm ?_
  refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
  simp only [Infra.ExpSemigroup.lapInt_def, map_smul]
  rw [hS ν ε P hν hε U hU t (le_of_lt ht) F]

/-- **The body resolvent solves the body equation** at `r = 2` (lines 1363-1372, 1409-1412; the
argument of `PartII-a:F07`): `R_μ g ∈ D₂` and `(μ + L)(R_μ g) = g`. -/
theorem bodyResolvent_bodyOp {P : ℝ} [Fact (0 < P)] (hP1 : P ≤ 1) {ν : ℝ} (hν : 0 < ν)
    {μ : ℂ} (hμ : 0 < μ.re + 1 / 4) (Rm : Yq P 2 →L[ℂ] Yq P 2) (hq : (2 : ℝ≥0∞) ≠ ⊤)
    (hRm : ∀ f, Rm f = ∫ t in Set.Ioi (0 : ℝ),
      Complex.exp (-(μ * t)) • B0421.phaseT (P := P) (q := 2) hq ν t f)
    (g : Yq P 2) : ∃ v : D P ν 2, (v : Yq P 2) = Rm g ∧ bodyOp P ν 2 μ v = g := by
  have h1 : (1 : ℝ≥0∞) < 2 := ENNReal.one_lt_two
  have h3 : (2 : ℝ≥0∞) < 3 := by norm_num
  have hμ' : 0 < μ.re + gammaR 2 := by rw [gammaR_two]; exact hμ
  have hsol : HasPhaseOp (fun Φ => μ • Φ + L0T ν Φ) (Rm g) g :=
    bodyResolvent_solves 2 h1 h3 P ν hν μ hμ' Rm hRm g
  have hmem : Rm g ∈ D P ν 2 :=
    commonBodyMaximalDomain 2 h1 h3 P hP1 ν hν μ hμ' (Rm g) g hsol
  have hL0 : HasPhaseOp (L0T ν) (Rm g) (g - μ • Rm g) := by
    intro Φ hΦ
    have h := hsol Φ hΦ
    simp only at h
    rw [phasePair_add (hΦ.const_smul μ) (isPhaseTest_L0T hΦ ν),
      phasePair_const_smul hΦ] at h
    rw [map_sub, map_smul, smul_eq_mul]
    linear_combination h
  refine ⟨⟨Rm g, hmem⟩, rfl, ?_⟩
  have hw : L0D (⟨Rm g, hmem⟩ : D P ν 2) = g - μ • Rm g := L0D_eq hL0
  simp only [bodyOp, LinearMap.add_apply, LinearMap.smul_apply, Submodule.coe_subtype,
    L0L_apply]
  rw [hw]
  abel

/-! ## The transported stress map on smooth tests (lines 1625-1632) -/

/-- **`U J_ε T_ε(s div_ε m) = (2π)^{-1/2}√(Pε) S_μ(𝒩_T m)`** for a real smooth tensor test `m`
(lines 1625-1632, 1639-1675; "the finite-curvature free inverse is the conjugate of the Cartesian
weak-stress inverse"): `chartConjSmooth` writes `J_ε T_ε G` as the outer Cartesian stress inverse
of `𝒩_T m`; `U` carries `(μ - A)⁻¹` to `R_μ`, `P_3D` to `lerayY` and the outer divergence to
`√(Pε)` times the phase divergence of the rows; `R_μ lerayY(div 𝒩_T m)` and `S_μ(𝒩_T m)` both
solve `(μ + L)w = lerayY(div 𝒩_T m)` in `D₂`, so they agree (`bg:common-body-graph`). -/
theorem phaseLift_liftVec_Teps (hS : PhaseSemigroupConj) (hL : PhaseLerayConj)
    (hD : PhaseDivScale) (hR : CartLiftRows)
    {ν ε c P : ℝ} [Fact (0 < P)] (hν : 0 < ν) (hε : 0 < ε) (hc : 0 < c) (hP : P = 2 * ε * c)
    (hP1 : P ≤ 1) {μ : ℂ} (hγ : 0 < μ.re + 1 / 4)
    {U : B0223.X SpaceC P →ₗᵢ[ℂ] Yq P 2} (hU : IsPhaseLift ε P U)
    (S : symY2 P →L[ℂ] Yq P 2) (hSw : IsWeakStressInverse P ν μ S)
    (m : Chart → Ten3) (hm : IsTensorTest c (fun p => tv4 (m p)))
    (G : HSpace c MeridC)
    (hG : (G : Profile → MeridC) =ᵐ[measureH c]
      (fun p => (p.1 : ℂ) • divEps ε (fun q => tv4 (m q)) p)) :
    ∃ X : symY2 P, (X : Y2Sym P) = smoothTensor P (cartRowsC (cartLift ε⁻¹ c m)) ∧
      U (B0223.liftVec hε hc hP (Teps hν hε hc hP μ G)) =
        (((Real.sqrt (2 * Real.pi))⁻¹ * Real.sqrt (P * ε) : ℝ) : ℂ) • S X := by
  have hμ4 : -(1 / 4 : ℝ) < μ.re := by linarith
  obtain ⟨hTest, hM, hCS⟩ :=
    UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.chartConjSmooth ν ε c P hν hε hc
      hP μ hμ4 m hm
  have hCSG := hCS G hG
  obtain ⟨hrows, hsym⟩ := hR ε c P hε hc hP m hm
  obtain ⟨Msub, hMS, hMmem⟩ := smoothSymSubmodule P
  have hXmem : smoothTensor P (cartRowsC (cartLift ε⁻¹ c m)) ∈ symY2 P :=
    hMS ((hMmem _).2 ⟨cartRowsC (cartLift ε⁻¹ c m), hrows, hsym, rfl⟩)
  refine ⟨⟨smoothTensor P (cartRowsC (cartLift ε⁻¹ c m)), hXmem⟩, rfl, ?_⟩
  obtain ⟨w, hwS, hwb⟩ := hSw ⟨smoothTensor P (cartRowsC (cartLift ε⁻¹ c m)), hXmem⟩
    (cartRowsC (cartLift ε⁻¹ c m)) hrows hsym rfl
  have h1 : (1 : ℝ≥0∞) < 2 := ENNReal.one_lt_two
  have h3 : (2 : ℝ≥0∞) < 3 := by norm_num
  have hμ' : 0 < μ.re + gammaR 2 := by rw [gammaR_two]; exact hγ
  obtain ⟨Rm, -, hRm⟩ := bodyResolvent_exists 2 h1 h3 P ν hν μ hμ'
  set g := testElem P 2 (tensorDiv (cartRowsC (cartLift ε⁻¹ c m))) with hgdef
  set V := hM.toLp (cartDiv (outerField ε⁻¹ (cartLift ε⁻¹ c m))) with hVdef
  have hCart : U (UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.CartStress hν hP μ
      (outerField ε⁻¹ (cartLift ε⁻¹ c m)) hM) =
      ((Real.sqrt (P * ε) : ℝ) : ℂ) • Rm (lerayY P 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top g) := by
    have e1 : UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.CartStress hν hP μ
        (outerField ε⁻¹ (cartLift ε⁻¹ c m)) hM =
        B0223.physRes (E := SpaceC) (P := P) hν ε μ (toX hP (B0226.P3D ε c V)) := rfl
    rw [e1, phaseLift_physRes hS hν hε hU hγ Rm _ hRm, hL ε c P hε hc hP U hU V,
      hD ε c P hε hc hP U hU _ hTest hM, map_smul, map_smul]
  obtain ⟨v, hv, hvb⟩ := bodyResolvent_bodyOp hP1 hν hγ Rm _ hRm
    (lerayY P 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top g)
  have hinj := bodyOp_injective_of_bound commonBodyGraphBound 2 h1 h3 P hP1 ν hν μ hμ'
  have hvw : v = w := hinj (hvb.trans hwb.symm)
  have hRS : Rm (lerayY P 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top g) =
      S ⟨smoothTensor P (cartRowsC (cartLift ε⁻¹ c m)), hXmem⟩ := by
    rw [← hv, hvw, hwS]
  rw [hCSG, map_smul, hCart, hRS, smul_smul]
  congr 1
  push_cast
  ring

/-- **The smooth-test bound for a real test** (`free:stress-energy` 1562-1564 transported,
`CartLiftNorm` 1644-1648): `‖T_ε(s div_ε m)‖_H ≤ ((Re μ + 1/4)ν)^{-1/2}‖m‖_{H_T}`. -/
theorem norm_Teps_real_le (hU : PhaseLiftExists) (hS : PhaseSemigroupConj)
    (hL : PhaseLerayConj) (hD : PhaseDivScale) (hR : CartLiftRows) (hN : CartLiftNorm)
    {ν ε c P : ℝ} [Fact (0 < P)] (hν : 0 < ν) (hε : 0 < ε) (hc : 0 < c) (hP : P = 2 * ε * c)
    (hP1 : P ≤ 1) {μ : ℂ} (hγ : 0 < μ.re + 1 / 4)
    (m : Chart → Ten3) (hm : IsTensorTest c (fun p => tv4 (m p))) (F : HTSpace c)
    (hF : (F : Profile → TensorVal) =ᵐ[measureHT c] (fun p => tv4 (m p)))
    (G : HSpace c MeridC)
    (hG : (G : Profile → MeridC) =ᵐ[measureH c]
      (fun p => (p.1 : ℂ) • divEps ε (fun q => tv4 (m q)) p)) :
    ‖Teps hν hε hc hP μ G‖ ≤ (Real.sqrt ((μ.re + 1 / 4) * ν))⁻¹ * ‖F‖ := by
  obtain ⟨U, hUl⟩ := hU ε P hε
  obtain ⟨S, hSw, hSb⟩ := weakStressExists P hP1 ν hν μ hγ
  obtain ⟨X, hX, hEq⟩ := phaseLift_liftVec_Teps hS hL hD hR hν hε hc hP hP1 hγ hUl S hSw m hm G hG
  have hpos2π : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have hnorm : ‖Teps hν hε hc hP μ G‖ =
      (Real.sqrt (2 * Real.pi))⁻¹ * Real.sqrt (P * ε) * ‖S X‖ := by
    rw [← (B0223.liftVec hε hc hP).norm_map, ← U.norm_map, hEq, norm_smul, Complex.norm_real,
      Real.norm_of_nonneg (by positivity)]
  have hSX : ‖S X‖ ≤ ‖(X : Y2Sym P)‖ / (2 * Real.sqrt ((μ.re + 1 / 4) * ν)) := (hSb X).1
  have hNm := hN ε c P hε hc hP m hm F hF
  rw [← hX] at hNm
  set a := Real.sqrt ((μ.re + 1 / 4) * ν) with ha_def
  have ha : 0 < a := Real.sqrt_pos.2 (mul_pos hγ hν)
  have hs2 : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  rw [hnorm]
  calc (Real.sqrt (2 * Real.pi))⁻¹ * Real.sqrt (P * ε) * ‖S X‖
      ≤ (Real.sqrt (2 * Real.pi))⁻¹ * Real.sqrt (P * ε) * (‖(X : Y2Sym P)‖ / (2 * a)) := by
        gcongr
    _ = (Real.sqrt (2 * Real.pi))⁻¹ * (Real.sqrt (P * ε) * ‖(X : Y2Sym P)‖) / (2 * a) := by
        ring
    _ ≤ (Real.sqrt (2 * Real.pi))⁻¹ * (Real.sqrt (2 * Real.pi) * Real.sqrt 2 * ‖F‖) /
          (2 * a) := by gcongr
    _ = Real.sqrt 2 / 2 * (a⁻¹ * ‖F‖) := by
        field_simp
    _ ≤ 1 * (a⁻¹ * ‖F‖) := by
        gcongr
        linarith
    _ = a⁻¹ * ‖F‖ := one_mul _

/-! ## The `ε > 0` bound on complex smooth tests -/

/-- **`near:free-energy` for `ε > 0` on smooth tests** (lines 1675-1683, `b`-part): for every
smooth tensor test `M`, `‖T_ε(s div_ε M)‖_H ≤ 2((Re μ + 1/4)ν)^{-1/2}‖M‖_{H_T}`. -/
def EpsSmoothBound : Prop :=
  ∀ (ν ε c P : ℝ) [Fact (0 < P)] (hν : 0 < ν) (hε : 0 < ε) (hc : 0 < c) (hP : P = 2 * ε * c),
    P ≤ 1 → ∀ μ : ℂ, 0 < μ.re + 1 / 4 →
    ∀ M : Profile → TensorVal, IsTensorTest c M → ∀ (F : HTSpace c) (G : HSpace c MeridC),
      (F : Profile → TensorVal) =ᵐ[measureHT c] M →
      (G : Profile → MeridC) =ᵐ[measureH c] (fun p => (p.1 : ℂ) • divEps ε M p) →
        ‖Teps hν hε hc hP μ G‖ ≤ 2 * (Real.sqrt ((μ.re + 1 / 4) * ν))⁻¹ * ‖F‖

theorem epsSmoothBound_of (hU : PhaseLiftExists) (hS : PhaseSemigroupConj)
    (hL : PhaseLerayConj) (hD : PhaseDivScale) (hR : CartLiftRows) (hN : CartLiftNorm)
    (hRI : TensorTestReIm) : EpsSmoothBound := by
  intro ν ε c P _ hν hε hc hP hP1 μ hγ M hM F G hF hG
  obtain ⟨m₁, m₂, hm₁, hm₂, -, hn₁, hn₂, hdiv⟩ := hRI c hc M hM
  have hMLp : MemLp M 2 (measureHT c) := (Lp.memLp F).ae_eq hF
  have hL₁ : MemLp (fun p => tv4 (m₁ p)) 2 (measureHT c) :=
    hMLp.of_le hm₁.smooth.continuous.aestronglyMeasurable (Eventually.of_forall hn₁)
  have hL₂ : MemLp (fun p => tv4 (m₂ p)) 2 (measureHT c) :=
    hMLp.of_le hm₂.smooth.continuous.aestronglyMeasurable (Eventually.of_forall hn₂)
  have hF₁n : ‖hL₁.toLp _‖ ≤ ‖F‖ := by
    refine Lp.norm_le_norm_of_ae_le ?_
    filter_upwards [hL₁.coeFn_toLp, hF] with p h1 h2
    rw [h1, h2]
    exact hn₁ p
  have hF₂n : ‖hL₂.toLp _‖ ≤ ‖F‖ := by
    refine Lp.norm_le_norm_of_ae_le ?_
    filter_upwards [hL₂.coeFn_toLp, hF] with p h1 h2
    rw [h1, h2]
    exact hn₂ p
  have hG₁L := UnforcedLeray.Short.PartIIIb.NearInst.Masked.tensorTestDivMem c ε hc _ hm₁
  have hG₂L := UnforcedLeray.Short.PartIIIb.NearInst.Masked.tensorTestDivMem c ε hc _ hm₂
  have hGsplit : G = hG₁L.toLp _ + Complex.I • hG₂L.toLp _ := by
    apply Lp.ext
    filter_upwards [hG, hG₁L.coeFn_toLp, hG₂L.coeFn_toLp,
      Lp.coeFn_add (hG₁L.toLp _) (Complex.I • hG₂L.toLp _),
      Lp.coeFn_smul Complex.I (hG₂L.toLp _)] with p h h1 h2 h3 h4
    rw [h, h3, Pi.add_apply, h4, Pi.smul_apply, h1, h2, hdiv ε p, smul_add,
      smul_comm (p.1 : ℂ) Complex.I]
  have hb₁ := norm_Teps_real_le hU hS hL hD hR hN hν hε hc hP hP1 hγ m₁ hm₁ _
    hL₁.coeFn_toLp _ hG₁L.coeFn_toLp
  have hb₂ := norm_Teps_real_le hU hS hL hD hR hN hν hε hc hP hP1 hγ m₂ hm₂ _
    hL₂.coeFn_toLp _ hG₂L.coeFn_toLp
  set a := (Real.sqrt ((μ.re + 1 / 4) * ν))⁻¹ with ha_def
  have ha : 0 ≤ a := by positivity
  rw [hGsplit, map_add, map_smul]
  calc ‖Teps hν hε hc hP μ (hG₁L.toLp _) + Complex.I • Teps hν hε hc hP μ (hG₂L.toLp _)‖
      ≤ ‖Teps hν hε hc hP μ (hG₁L.toLp _)‖ +
          ‖Complex.I • Teps hν hε hc hP μ (hG₂L.toLp _)‖ := norm_add_le _ _
    _ = ‖Teps hν hε hc hP μ (hG₁L.toLp _)‖ + ‖Teps hν hε hc hP μ (hG₂L.toLp _)‖ := by
        rw [norm_smul, Complex.norm_I, one_mul]
    _ ≤ a * ‖hL₁.toLp _‖ + a * ‖hL₂.toLp _‖ := add_le_add hb₁ hb₂
    _ ≤ a * ‖F‖ + a * ‖F‖ := by gcongr
    _ = 2 * a * ‖F‖ := by ring

/-! ## The target -/

/-- `((Re μ + 1/4)ν)^{-1/2} ≤ (1 + M + γ_*⁻¹) ν^{-1/2}` for `γ_* ≤ Re μ + 1/4`, `‖μ‖ ≤ M`. -/
theorem inv_sqrt_le_window {ν M γs : ℝ} {μ : ℂ} (hν : 0 < ν) (hγs : 0 < γs)
    (hμM : ‖μ‖ ≤ M) (hγ : γs ≤ μ.re + 1 / 4) :
    (Real.sqrt ((μ.re + 1 / 4) * ν))⁻¹ ≤ (1 + M + γs⁻¹) * ν ^ (-(1 / 2 : ℝ)) := by
  have ha : 0 < μ.re + 1 / 4 := lt_of_lt_of_le hγs hγ
  have hM0 : 0 ≤ M := le_trans (norm_nonneg μ) hμM
  have hsν : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
  have hνr : ν ^ (-(1 / 2 : ℝ)) = (Real.sqrt ν)⁻¹ := by
    rw [Real.rpow_neg hν.le, Real.sqrt_eq_rpow]
  rw [hνr, Real.sqrt_mul ha.le, mul_inv]
  refine mul_le_mul_of_nonneg_right ?_ (inv_nonneg.2 hsν.le)
  have hsγ : 0 < Real.sqrt γs := Real.sqrt_pos.2 hγs
  have h1 : (Real.sqrt (μ.re + 1 / 4))⁻¹ ≤ (Real.sqrt γs)⁻¹ :=
    inv_anti₀ hsγ (Real.sqrt_le_sqrt hγ)
  have h2 : (Real.sqrt γs)⁻¹ ≤ 1 + γs⁻¹ := by
    set u := (Real.sqrt γs)⁻¹ with hu
    have hu2 : u ^ 2 = γs⁻¹ := by
      rw [hu, inv_pow, Real.sq_sqrt hγs.le]
    nlinarith [sq_nonneg (u - 1)]
  linarith

/-- **`near:free-energy`, `b`-part, with the stress maps** (lines 1675-1689): from the smooth-test
bounds for `ε > 0` (`EpsSmoothBound`) and `ε = 0` (`FlatSmoothBound`) by completion from smooth
tensors (`StressCompletion`), with `C = 2`. -/
theorem nearStressMapExists_of (hE : EpsSmoothBound) (hFl : FlatSmoothBound)
    (hC : StressCompletion) : NearStressMapExists := by
  refine ⟨2, by norm_num, ?_⟩
  intro ν c M γs hν hc hγs ε hε _ P _ hP hP1 μ hμM hγ
  have ha : 0 < μ.re + 1 / 4 := lt_of_lt_of_le hγs hγ
  set K := (Real.sqrt ((μ.re + 1 / 4) * ν))⁻¹ with hK_def
  have hK0 : 0 ≤ K := by positivity
  have hKle : K ≤ (1 + M + γs⁻¹) * ν ^ (-(1 / 2 : ℝ)) := inv_sqrt_le_window hν hγs hμM hγ
  constructor
  · obtain ⟨S, hS, hSb⟩ := hC c ε hc (Teps hν hε hc hP μ) (2 * K) (by positivity)
      (fun M' hM' F G hF hG => hE ν ε c P hν hε hc hP hP1 μ ha M' hM' F G hF hG)
    refine ⟨S, hS, fun F => (hSb F).trans ?_⟩
    have h2 : 2 * K ≤ 2 * (1 + M + γs⁻¹) * ν ^ (-(1 / 2 : ℝ)) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hKle (by norm_num)
    exact mul_le_mul_of_nonneg_right h2 (norm_nonneg F)
  · obtain ⟨S, hS, hSb⟩ := hC c 0 hc (T0flat hc ν μ) K hK0
      (fun M' hM' F G hF hG => hFl ν c hc hν μ ha M' hM' F G hF hG)
    refine ⟨S, hS, fun F => (hSb F).trans ?_⟩
    have hR0 : 0 ≤ (1 + M + γs⁻¹) * ν ^ (-(1 / 2 : ℝ)) := le_trans hK0 hKle
    have h2 : K ≤ 2 * (1 + M + γs⁻¹) * ν ^ (-(1 / 2 : ℝ)) := by
      rw [mul_assoc]
      linarith
    exact mul_le_mul_of_nonneg_right h2 (norm_nonneg F)

/-- **`PartII-a:N01` from the eight leaves of `Sub/N01/Defs.lean`** (tasks `PartII-a:N01/1` … `/8`)
and the flat smooth-test bound (`Sub/N01/FlatReduction.lean`). -/
theorem nearStressMapExists_of_parts (h1 : PhaseLiftExists) (h2 : PhaseSemigroupConj)
    (h3 : PhaseLerayConj) (h4 : PhaseDivScale) (h5 : CartLiftRows) (h6 : CartLiftNorm)
    (h7 : TensorTestReIm) (h8 : StressCompletion) (h9 : FlatSmoothBound) :
    NearStressMapExists :=
  nearStressMapExists_of (epsSmoothBound_of h1 h2 h3 h4 h5 h6 h7) h9 h8

end UnforcedLeray.Short.PartIIa.N01
