import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_9
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.Org.YThinTrans.ShiftedResolvent
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_4.YRepStream.SepYoungRep.MemLp
import UnforcedLeray.Short.PartIIIa.T16_SepYoung
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.Sub.T8_4

/-!
# `PartIII-b:C/ward/9/2`: the young `L²` bound of `χ_yW_μ`

Source `the November 2 reference manuscript` 3631-3648 (`sep:young`, `p = q = 2`,
`b = 1`, `j = 0`), 2683-2689 (lift identity), 4163-4168.

For old `L²` data `g` the source `T = oldCutSrc R c (R√(5ν/6)) g` is a separated source with the same
`sepW` responses as `oldPhys R c g`, and the lift identity gives
`‖T‖_{L²_τL²} ≤ √π R ‖g‖_{L²(s^{-1/2}dς)}`.  `sep:young` bounds the young cut of `sepWre ν μ T` by
`C D^{-1}‖T‖`, and the chart transport (`chartYoungTransport`) turns the physical young norm into the
chart reading; `|χ_y| ≤ 1`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

private theorem l2_euclid_re_le (w : Fin 3 → ℂ) :
    ‖(WithLp.toLp 2 fun i => (w i).re : Space)‖ ≤ Real.sqrt 3 * ‖w‖ := by
  rw [EuclideanSpace.norm_eq]
  have h : ∀ i, ‖(WithLp.toLp 2 fun i => (w i).re : Space) i‖ ^ 2 ≤ ‖w‖ ^ 2 := by
    intro i
    have h1 : ‖(WithLp.toLp 2 fun i => (w i).re : Space) i‖ ≤ ‖w i‖ := by
      simpa using Complex.abs_re_le_norm (w i)
    exact pow_le_pow_left₀ (norm_nonneg _) (h1.trans (norm_le_pi_norm w i)) 2
  calc Real.sqrt (∑ i, ‖(WithLp.toLp 2 fun i => (w i).re : Space) i‖ ^ 2)
      ≤ Real.sqrt (∑ _i : Fin 3, ‖w‖ ^ 2) := Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => h i)
    _ = Real.sqrt 3 * ‖w‖ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (norm_nonneg _)]
      norm_num

/-! ## 1. `sep:young` with `p = q = 2`, `b = 1` -/

private theorem l2_sepWreYoung (μ : ℝ) (hμ : -(1 / 4) < μ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ν R P : ℝ, 0 < ν → 0 < R → 0 < P →
      ∀ T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ,
      IIIa.IsSepSource P (R * Real.sqrt (5 * ν / 6)) T →
      IIIa.ltauLq P 2 (fun τ y => if R * Real.sqrt ν ≤ Real.sqrt (y 0 ^ 2 + y 1 ^ 2)
          then ‖sepWre ν μ T τ y‖ₑ else 0) ≤
        ENNReal.ofReal (C * (R * Real.sqrt ν)⁻¹) * IIIa.ltauLq P 2 (IIIa.srcNorm T) := by
  have hK : IsCompact ({(μ : ℂ)} : Set ℂ) := isCompact_singleton
  have hKre : ∀ m ∈ ({(μ : ℂ)} : Set ℂ), -(1 / 4) < m.re := by
    rintro m rfl
    simpa using hμ
  obtain ⟨C0, hC0, hC⟩ := IIIa.sepYoung _ hK hKre 0 2 2 1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by
      refine ⟨2 * μ + 3 / 2, ?_, ?_⟩
      · linarith
      · rintro m rfl
        simp only [Complex.ofReal_re]
        norm_num)
  have hs : Real.sqrt (5 / 6) < 1 := by
    rw [Real.sqrt_lt' one_pos]; norm_num
  have hs0 : 0 < Real.sqrt (5 / 6) := Real.sqrt_pos.2 (by norm_num)
  set c : ℝ := 1 - Real.sqrt (5 / 6) with hcdef
  have hc : 0 < c := by rw [hcdef]; linarith
  refine ⟨Real.sqrt 3 * C0 * c⁻¹, by positivity, ?_⟩
  intro ν R P hν hR hP T hT
  have hsν : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
  have hrOut : Real.sqrt (5 * ν / 6) = Real.sqrt (5 / 6) * Real.sqrt ν := by
    rw [← Real.sqrt_mul (by norm_num)]; congr 1; ring
  have hrIn : 0 < R * Real.sqrt ν := mul_pos hR hsν
  have hD : R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6) = c * (R * Real.sqrt ν) := by
    rw [hrOut, hcdef]; ring
  have hlt : R * Real.sqrt (5 * ν / 6) < R * Real.sqrt ν := by
    have : 0 < c * (R * Real.sqrt ν) := mul_pos hc hrIn
    linarith
  have hnn : 0 ≤ R * Real.sqrt (5 * ν / 6) := by positivity
  have h1 := hC ν hν (μ : ℂ) rfl (R * Real.sqrt (5 * ν / 6)) (R * Real.sqrt ν) P
    hnn hlt hP T hT
  have he : (-4 - ((0 : ℕ) : ℝ) + 3 / 1 : ℝ) = -1 := by norm_num
  rw [hD, he, Real.rpow_neg_one, mul_inv] at h1
  have hpt : ∀ τ y, (if R * Real.sqrt ν ≤ Real.sqrt (y 0 ^ 2 + y 1 ^ 2)
        then ‖sepWre ν μ T τ y‖ₑ else 0) ≤
      ENNReal.ofReal (Real.sqrt 3) * IIIa.youngDerivNorm ν (μ : ℂ) T 0 (R * Real.sqrt ν) τ y := by
    intro τ y
    unfold IIIa.youngDerivNorm
    split_ifs with hy
    · unfold IIIa.wDerivNorm
      rw [← ofReal_norm, ← ofReal_norm, norm_iteratedFDeriv_zero,
        ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (l2_euclid_re_le _)
    · simp
  calc IIIa.ltauLq P 2 (fun τ y => if R * Real.sqrt ν ≤ Real.sqrt (y 0 ^ 2 + y 1 ^ 2)
          then ‖sepWre ν μ T τ y‖ₑ else 0)
      ≤ IIIa.ltauLq P 2 (fun τ y => ENNReal.ofReal (Real.sqrt 3) *
          IIIa.youngDerivNorm ν (μ : ℂ) T 0 (R * Real.sqrt ν) τ y) :=
        IIIa.ltauLq_mono P 2 (by norm_num) hpt
    _ = ENNReal.ofReal (Real.sqrt 3) *
          IIIa.ltauLq P 2 (IIIa.youngDerivNorm ν (μ : ℂ) T 0 (R * Real.sqrt ν)) :=
        IIIa.ltauLq_const_mul P 2 (by norm_num) _ ENNReal.ofReal_ne_top _
    _ ≤ ENNReal.ofReal (Real.sqrt 3) * (ENNReal.ofReal (C0 * (c⁻¹ *
          (R * Real.sqrt ν)⁻¹)) * IIIa.ltauLq P 2 (IIIa.srcNorm T)) :=
        by gcongr
    _ = _ := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
        congr 2
        ring

/-! ## 2. The separated source of an old `L²` datum and the lift identity -/

private theorem l2_bridge (R c ν : ℝ) (hR : 0 < R) (hc : 0 < c) (hν : 0 < ν)
    (g : Chart → Ten3) (hg : IsOldL2 c ν g) :
    IIIa.IsSepSource (2 * c / R) (R * Real.sqrt (5 * ν / 6))
        (oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g) ∧
      IsAxiSource (oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g) ∧
      (∀ (μ : ℂ) (y : Space) (τ : ℝ),
        IIIa.sepW ν μ (oldPhys R c g) y τ =
          IIIa.sepW ν μ (oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g) y τ) ∧
      IIIa.ltauLq (2 * c / R) 2 (IIIa.srcNorm (oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g)) ≤
        ENNReal.ofReal (Real.sqrt Real.pi * R) * eLpNorm g 2 (ageμ c (-1 / 2)) := by
  have hgm := hg.measurable
  have hpull := chartOfNullPullback R c hR hc _ (ae_iff.1 hg.old)
  have hagree : ∀ᵐ x : ℝ × Space ∂volume, oldPhys R c g x.1 x.2 =
      oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g x.1 x.2 := by
    filter_upwards [hpull] with x hx
    simp only [Set.mem_setOf_eq, not_not] at hx
    unfold oldCutSrc
    split_ifs with hz
    · rfl
    · have h0r : 0 ≤ R * Real.sqrt (5 * ν / 6) := by positivity
      have hlt := not_le.1 hz
      have hpos : 0 < NearInst.hRad x.2 := lt_of_le_of_lt h0r hlt
      have hsq : (R * Real.sqrt (5 * ν / 6)) ^ 2 = R ^ 2 * (5 * ν / 6) := by
        rw [mul_pow, Real.sq_sqrt (by positivity)]
      have hlt2 : (R * Real.sqrt (5 * ν / 6)) ^ 2 < NearInst.hRad x.2 ^ 2 := by
        nlinarith
      have hs : ν * (NearInst.chartOf R c x.2 x.1).1 ≤ 6 / 5 := by
        show ν * (R ^ 2 / NearInst.hRad x.2 ^ 2) ≤ 6 / 5
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]
        nlinarith
      have hG0 := hx hs
      simp only [oldPhys, NearInst.cartLift, hG0, rb_nsSym_zero, smul_zero, Matrix.mul_zero,
        Matrix.zero_mul]
  have hper : ∀ τ z, oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g (τ + 2 * c / R) z =
      oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g τ z := by
    intro τ z
    unfold oldCutSrc
    rw [oldPhysPeriodic R c g τ z]
  have hsupp : ∀ τ z, R * Real.sqrt (5 * ν / 6) < Real.sqrt (z 0 ^ 2 + z 1 ^ 2) →
      oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g τ z = 0 := by
    intro τ z hz
    have hz' : ¬ NearInst.hRad z ≤ R * Real.sqrt (5 * ν / 6) := not_le.2 hz
    unfold oldCutSrc
    simp only [hz', ite_false]
  refine ⟨⟨oldCutMeasurable R c _ g hgm, hper, hsupp⟩, ?_,
    fun μ y τ => sepWCongrAE ν μ _ _ hagree y τ, ?_⟩
  · unfold IsAxiSource
    refine ⟨fun co si hco τ z => ?_, fun τ z => ?_⟩
    · unfold oldCutSrc
      rw [rot_hRad co si hco z]
      split_ifs with hz
      · exact oldPhysRotEquiv co si hco R c g τ z
      · simp
    · unfold oldCutSrc
      rw [refl_hRad z]
      split_ifs with hz
      · exact oldPhysReflEquiv R c g τ z
      · simp
  · -- the lift identity
    set P : ℝ := 2 * c / R with hPdef
    have hP0 : 0 < P := div_pos (mul_pos two_pos hc) hR
    set I : ℝ≥0∞ := ∫⁻ p, ‖g p‖ₑ ^ 2 ∂(ageμ c (-1 / 2)) with hI
    have hG2 : Measurable fun p : Chart => ‖g p‖ₑ ^ 2 := hgm.enorm.pow_const 2
    have hFm : Measurable fun p : Chart => ENNReal.ofReal (p.1 ^ 2) * ‖g p‖ₑ ^ 2 :=
      ((measurable_fst.pow_const 2).ennreal_ofReal).mul hG2
    have hAW : ∫⁻ p, ENNReal.ofReal (p.1 ^ 2) * ‖g p‖ₑ ^ 2 ∂(ageμ c (-5 / 2)) = I :=
      ageWeightShift c hc _ hG2
    have hMain := chartPhaseLIntegral R c hR hc _ hFm
    rw [hAW] at hMain
    have hB : ∫⁻ τ in Ioc 0 P,
        (∫⁻ y, IIIa.srcNorm (oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g) τ y ^ (2 : ℝ)) ^
          ((2 : ℝ) / 2) ≤ ENNReal.ofReal P * (ENNReal.ofReal (Real.pi * R ^ 2) * I) := by
      rw [← mul_assoc, ← hMain]
      refine lintegral_mono fun τ => ?_
      rw [show (2 : ℝ) / 2 = 1 by norm_num, ENNReal.rpow_one]
      exact lintegral_mono fun z => oldCut_sq_le R c _ g τ z
    have hPne : ENNReal.ofReal P ≠ 0 := (ENNReal.ofReal_pos.2 hP0).ne'
    have hX : (ENNReal.ofReal P)⁻¹ * ∫⁻ τ in Ioc 0 P,
        (∫⁻ y, IIIa.srcNorm (oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g) τ y ^ (2 : ℝ)) ^
          ((2 : ℝ) / 2) ≤ ENNReal.ofReal (Real.pi * R ^ 2) * I := by
      calc _ ≤ (ENNReal.ofReal P)⁻¹ * (ENNReal.ofReal P *
            (ENNReal.ofReal (Real.pi * R ^ 2) * I)) := by gcongr
        _ = _ := by rw [← mul_assoc, ENNReal.inv_mul_cancel hPne ENNReal.ofReal_ne_top, one_mul]
    unfold IIIa.ltauLq
    calc ((ENNReal.ofReal P)⁻¹ * ∫⁻ τ in Ioc 0 P,
        (∫⁻ y, IIIa.srcNorm (oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g) τ y ^ (2 : ℝ)) ^
          ((2 : ℝ) / 2)) ^ (1 / 2 : ℝ)
        ≤ (ENNReal.ofReal (Real.pi * R ^ 2) * I) ^ (1 / 2 : ℝ) :=
          ENNReal.rpow_le_rpow hX (by norm_num)
      _ = ENNReal.ofReal (Real.sqrt Real.pi * R) * eLpNorm g 2 (ageμ c (-1 / 2)) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
          congr 1
          · rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
            congr 1
            rw [← Real.sqrt_eq_rpow, Real.sqrt_mul Real.pi_pos.le, Real.sqrt_sq hR.le]
          · rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
            simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two, hI]

/-! ## 3. Chart facts -/

private theorem l2_meridPt_chartY {R : ℝ} (hR : 0 < R) {q : Chart} (hs : 0 < q.1) :
    meridPt (NearInst.chartY R q) = NearInst.chartY R q := by
  have h := wyl_ϱ_chartY hR hs
  unfold meridPt
  rw [h]
  ext i
  fin_cases i <;> simp [NearInst.chartY]

private theorem l2_chartY_not_axis {R : ℝ} (hR : 0 < R) {q : Chart} (hs : 0 < q.1) :
    NearInst.chartY R q ∉ axis := by
  intro h
  have h' : NearInst.chartY R q 0 = 0 ∧ NearInst.chartY R q 1 = 0 := h
  have h1 : NearInst.chartY R q 0 = R / Real.sqrt q.1 := by simp [NearInst.chartY]
  have hne : R / Real.sqrt q.1 ≠ 0 := div_ne_zero hR.ne' (Real.sqrt_pos.2 hs).ne'
  exact hne (h1 ▸ h'.1)

/-- For an axisymmetric swirl-free field the norm at a chart receiver is `√s` times the norm of
the chart coefficient. -/
private theorem l2_norm_eq {R : ℝ} (hR : 0 < R) {F : ℝ → Space → Space} (hax : AxiNoSwirl F)
    {q : Chart} (hs : 0 < q.1) :
    ‖F (NearInst.chartTau R q) (NearInst.chartY R q)‖ = Real.sqrt q.1 * ‖coefOf R F q‖ := by
  have hy := l2_chartY_not_axis hR hs
  have hm := l2_meridPt_chartY hR hs
  have h := hax (NearInst.chartTau R q) (NearInst.chartY R q) (mem_univ _) hy
  rw [hm] at h
  have hsq : 0 < Real.sqrt q.1 := Real.sqrt_pos.2 hs
  unfold coefOf
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hsq.le), ← mul_assoc,
    mul_inv_cancel₀ hsq.ne', one_mul]
  conv_lhs => rw [h]
  exact norm_frameL hy _

private theorem l2_cond {R ν : ℝ} (hR : 0 < R) (hν : 0 < ν) {q : Chart} (hs : 0 < q.1)
    (hp : ν * q.1 ≤ 1) :
    R * Real.sqrt ν ≤ Real.sqrt (NearInst.chartY R q 0 ^ 2 + NearInst.chartY R q 1 ^ 2) := by
  have hsq : 0 < Real.sqrt q.1 := Real.sqrt_pos.2 hs
  have hY0 : (NearInst.chartY R q) 0 = R / Real.sqrt q.1 := by simp [NearInst.chartY]
  have hY1 : (NearInst.chartY R q) 1 = 0 := by simp [NearInst.chartY]
  rw [hY0, hY1]
  have hpos : 0 ≤ R / Real.sqrt q.1 := by positivity
  rw [show (R / Real.sqrt q.1) ^ 2 + (0 : ℝ) ^ 2 = (R / Real.sqrt q.1) ^ 2 by ring,
    Real.sqrt_sq hpos, le_div_iff₀ hsq]
  have h1 : Real.sqrt ν * Real.sqrt q.1 ≤ 1 := by
    rw [← Real.sqrt_mul hν.le]
    exact Real.sqrt_le_one.2 hp
  nlinarith

private theorem l2_chartTau_meas (R : ℝ) : Measurable fun p : Chart => NearInst.chartTau R p := by
  unfold NearInst.chartTau
  exact (((measurable_fst.comp measurable_snd).const_mul 2).div_const R).add
    (Real.measurable_log.comp measurable_fst)

private theorem l2_chartY_meas (R : ℝ) : Measurable fun p : Chart => NearInst.chartY R p := by
  have hsq : Measurable fun p : Chart => Real.sqrt p.1 :=
    Real.continuous_sqrt.measurable.comp measurable_fst
  unfold NearInst.chartY
  exact T8_4.t84_vec3 (a := fun p : Chart => R / Real.sqrt p.1) (b := fun _ => (0 : ℝ))
    (c := fun p : Chart => p.2.2 / Real.sqrt p.1)
    (measurable_const.div hsq) measurable_const
    ((measurable_snd.comp measurable_snd).div hsq)

/-! ## 4. The theorem -/

theorem wardYWYoungL2_proved : WardYWYoungL2 := by
  intro ν μ R c χy hχy hν hR hc hμ
  obtain ⟨C0, hC0, hY⟩ := l2_sepWreYoung μ hμ
  refine ⟨C0 * (R * Real.sqrt ν)⁻¹, ?_⟩
  intro g hg
  obtain ⟨hS, hAx, hresp, hB⟩ := l2_bridge R c ν hR hc hν g hg
  set T := oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g with hTdef
  have hP : 0 < 2 * c / R := div_pos (mul_pos two_pos hc) hR
  have hW : wardW ν μ R c g = sepWre ν μ T :=
    funext fun τ => funext fun y => by simp only [wardW, sepWre, hresp]
  set N : ℝ≥0∞ := eLpNorm g 2 (ageμ c (-1 / 2)) with hNdef
  have hN : N < ⊤ := hg.memLp.eLpNorm_lt_top
  have hmom : SepMoment (2 * c / R) T :=
    lt_of_le_of_lt hB (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hN)
  have hsrc := hY ν R (2 * c / R) hν hR hP T hS
  -- the young cut of `sepWre`
  have hGm := sepYoungCut_measurable R ν μ hν T (fun i j => hS.measurable i j)
  have hGax := sepYoungCut_axi R ν μ (2 * c / R) hR hν hμ T hP hS hmom sepWEquivariance hAx
  have hGper : ∀ τ y, sepYoungCut R ν μ T (τ + 2 * c / R) y = sepYoungCut R ν μ T τ y :=
    fun τ y => sepYoungCut_periodic _ _ _ _ T hS.periodic τ y
  have hYT := chartYoungTransport R c ν hR hc hν (sepYoungCut R ν μ T) hGm hGax hGper
  have hcutG : (fun τ y => if R * Real.sqrt ν ≤ Real.sqrt (y 0 ^ 2 + y 1 ^ 2) then
      ‖sepYoungCut R ν μ T τ y‖ₑ else 0) =
      (fun τ y => if R * Real.sqrt ν ≤ Real.sqrt (y 0 ^ 2 + y 1 ^ 2) then
      ‖sepWre ν μ T τ y‖ₑ else 0) := by
    funext τ y
    by_cases h : R * Real.sqrt ν ≤ Real.sqrt (y 0 ^ 2 + y 1 ^ 2)
    · simp only [sepYoungCut, if_pos h]
    · simp only [if_neg h]
  rw [hcutG] at hYT
  set A : ℝ≥0∞ := IIIa.ltauLq (2 * c / R) 2 (fun τ y =>
    if R * Real.sqrt ν ≤ Real.sqrt (y 0 ^ 2 + y 1 ^ 2) then ‖sepWre ν μ T τ y‖ₑ else 0) with hAdef
  have hAle : A ≤ ENNReal.ofReal (C0 * (R * Real.sqrt ν)⁻¹) *
      (ENNReal.ofReal (Real.sqrt Real.pi * R) * N) := hsrc.trans (by gcongr)
  -- measurability of the reading
  have hFm : Measurable fun x : ℝ × Space => wardYoungW ν μ R c χy g x.1 x.2 := by
    have hWm : Measurable fun x : ℝ × Space => sepWre ν μ T x.1 x.2 :=
      sepWre_measurable ν μ hν T (fun i j => hS.measurable i j)
    have hχm : Measurable fun x : ℝ × Space => χy (ν * age R x.2) := by
      have h1 : Measurable fun x : ℝ × Space => ν * age R x.2 := by
        unfold age
        have hϱ : Measurable fun x : ℝ × Space => ϱ x.2 :=
          continuous_ϱ.measurable.comp measurable_snd
        exact measurable_const.mul (measurable_const.div (hϱ.pow_const 2))
      exact hχy.smooth.continuous.measurable.comp h1
    have : (fun x : ℝ × Space => wardYoungW ν μ R c χy g x.1 x.2) =
        fun x => χy (ν * age R x.2) • sepWre ν μ T x.1 x.2 := by
      funext x
      simp only [wardYoungW, hW]
    rw [this]
    exact hχm.smul hWm
  have hSm : MeasurableSet (wardYoungSet ν) := by
    unfold wardYoungSet
    exact measurableSet_le (measurable_fst.const_mul ν) measurable_const
  have hsq : Measurable fun p : Chart => Real.sqrt p.1 :=
    Real.continuous_sqrt.measurable.comp measurable_fst
  have hRm : Measurable (wardYoungRead ν R (wardYoungW ν μ R c χy g)) := by
    unfold wardYoungRead
    exact (((measurable_inv.comp hsq).mul
      (hFm.comp ((l2_chartTau_meas R).prodMk (l2_chartY_meas R))).norm)).indicator hSm
  refine ⟨hRm.aestronglyMeasurable, ?_⟩
  -- pointwise domination by the chart coefficient of the young cut
  have hpt : ∀ q : Chart, ‖wardYoungRead ν R (wardYoungW ν μ R c χy g) q‖ₑ ^ (2 : ℝ) ≤
      {p : Chart | ν * p.1 ≤ 1}.indicator
        (fun p => ‖coefOf R (sepYoungCut R ν μ T) p‖ₑ ^ (2 : ℝ)) q := by
    intro q
    by_cases hq : ν * q.1 ≤ 1
    · rw [indicator_of_mem (show q ∈ {p : Chart | ν * p.1 ≤ 1} from hq)]
      refine ENNReal.rpow_le_rpow ?_ (by norm_num)
      rcases le_or_gt q.1 0 with hs | hs
      · rw [wyl_youngRead_zero_of_nonpos _ hs]
        simp
      · rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [Real.norm_of_nonneg (wyl_youngRead_nonneg _ _ _ _),
          wyl_youngRead_of_young _ hq]
        have hsq0 : 0 < Real.sqrt q.1 := Real.sqrt_pos.2 hs
        have hc1 : R * Real.sqrt ν ≤ Real.sqrt (NearInst.chartY R q 0 ^ 2 +
            NearInst.chartY R q 1 ^ 2) := l2_cond hR hν hs hq
        have hcut : sepYoungCut R ν μ T (NearInst.chartTau R q) (NearInst.chartY R q) =
            sepWre ν μ T (NearInst.chartTau R q) (NearInst.chartY R q) := by
          simp only [sepYoungCut, if_pos hc1]
        have hnorm := l2_norm_eq hR hGax hs (q := q)
        have hχ := hχy.range (ν * age R (NearInst.chartY R q))
        have hle : ‖wardYoungW ν μ R c χy g (NearInst.chartTau R q) (NearInst.chartY R q)‖ ≤
            ‖sepWre ν μ T (NearInst.chartTau R q) (NearInst.chartY R q)‖ := by
          simp only [wardYoungW, hW]
          rw [norm_smul, Real.norm_of_nonneg hχ.1]
          exact mul_le_of_le_one_left (norm_nonneg _) hχ.2
        calc (Real.sqrt q.1)⁻¹ *
              ‖wardYoungW ν μ R c χy g (NearInst.chartTau R q) (NearInst.chartY R q)‖
            ≤ (Real.sqrt q.1)⁻¹ * ‖sepYoungCut R ν μ T (NearInst.chartTau R q)
                (NearInst.chartY R q)‖ := by
              rw [hcut]
              exact mul_le_mul_of_nonneg_left hle (inv_nonneg.2 hsq0.le)
          _ = ‖coefOf R (sepYoungCut R ν μ T) q‖ := by
              rw [hnorm, ← mul_assoc, inv_mul_cancel₀ hsq0.ne', one_mul]
    · rw [indicator_of_notMem (show q ∉ {p : Chart | ν * p.1 ≤ 1} from hq)]
      have : wardYoungRead ν R (wardYoungW ν μ R c χy g) q = 0 := by
        unfold wardYoungRead
        rw [indicator_of_notMem (show q ∉ wardYoungSet ν from hq)]
      rw [this]
      simp
  have hYm : MeasurableSet {p : Chart | ν * p.1 ≤ 1} := hSm
  have hint : ∫⁻ q, ‖wardYoungRead ν R (wardYoungW ν μ R c χy g) q‖ₑ ^ (2 : ℝ)
        ∂(ageμ c (-3 / 2)) ≤ ENNReal.ofReal (1 / (Real.pi * R ^ 2)) * A ^ (2 : ℝ) := by
    calc _ ≤ ∫⁻ q, {p : Chart | ν * p.1 ≤ 1}.indicator
          (fun p => ‖coefOf R (sepYoungCut R ν μ T) p‖ₑ ^ (2 : ℝ)) q ∂(ageμ c (-3 / 2)) :=
          lintegral_mono hpt
      _ = ∫⁻ p in {p : Chart | ν * p.1 ≤ 1}, ‖coefOf R (sepYoungCut R ν μ T) p‖ₑ ^ (2 : ℝ)
          ∂(ageμ c (-3 / 2)) := lintegral_indicator hYm _
      _ ≤ _ := hYT
  have hpi : 0 < Real.pi * R ^ 2 := by positivity
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat]
  calc (∫⁻ q, ‖wardYoungRead ν R (wardYoungW ν μ R c χy g) q‖ₑ ^ (2 : ℝ)
        ∂(ageμ c (-3 / 2))) ^ (1 / (2 : ℝ))
      ≤ (ENNReal.ofReal (1 / (Real.pi * R ^ 2)) * A ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) :=
        ENNReal.rpow_le_rpow hint (by norm_num)
    _ = ENNReal.ofReal (1 / (Real.sqrt Real.pi * R)) * A := by
        have key : ENNReal.ofReal (1 / (Real.pi * R ^ 2)) ^ (1 / (2 : ℝ)) =
            ENNReal.ofReal (1 / (Real.sqrt Real.pi * R)) := by
          rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
          congr 1
          rw [← Real.sqrt_eq_rpow, one_div, Real.sqrt_inv, Real.sqrt_mul Real.pi_pos.le,
            Real.sqrt_sq hR.le, one_div]
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), key, ← ENNReal.rpow_mul]
        norm_num
    _ ≤ ENNReal.ofReal (1 / (Real.sqrt Real.pi * R)) *
          (ENNReal.ofReal (C0 * (R * Real.sqrt ν)⁻¹) *
            (ENNReal.ofReal (Real.sqrt Real.pi * R) * N)) := by gcongr
    _ = ENNReal.ofReal (C0 * (R * Real.sqrt ν)⁻¹) * N := by
        have hk : 0 < Real.sqrt Real.pi * R := mul_pos (Real.sqrt_pos.2 Real.pi_pos) hR
        rw [← mul_assoc, mul_comm (ENNReal.ofReal (1 / _)) (ENNReal.ofReal _), mul_assoc,
          ← mul_assoc (ENNReal.ofReal (1 / _)), ← ENNReal.ofReal_mul (by positivity),
          one_div, inv_mul_cancel₀ hk.ne', ENNReal.ofReal_one, one_mul]

end UnforcedLeray.Short.PartIIIb.Concrete
