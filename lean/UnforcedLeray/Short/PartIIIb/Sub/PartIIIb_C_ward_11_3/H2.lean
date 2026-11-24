import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_11_3.H1

/-!
# Helpers for `wardDYYoungL2_proved` (2): `∂_j(streamCorr (sepWre))` on the young support
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- The truncated modulus of the outward primitive of `sepWre ν μ T` on `ϱ y ≤ r2`. -/
def w2NW (ν μ R c r2 : ℝ) (g : Chart → Ten3) (τ : ℝ) (y : Space) : ℝ :=
  if ϱ y ≤ r2 then
    |outPrim (sepWre ν μ (oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g)) τ (ϱ y) (y 2)|
  else 0

/-- The corresponding vertical field. -/
def w2PhiW (ν μ R c r2 : ℝ) (g : Chart → Ten3) (τ : ℝ) (y : Space) : Space :=
  w2NW ν μ R c r2 g τ y • coordinateVector 2

theorem w2NW_nonneg (ν μ R c r2 : ℝ) (g : Chart → Ten3) (τ : ℝ) (y : Space) :
    0 ≤ w2NW ν μ R c r2 g τ y := by
  unfold w2NW; split_ifs <;> positivity

theorem w2NW_meridPt (ν μ R c r2 : ℝ) (g : Chart → Ten3) (τ : ℝ) (y : Space) :
    w2NW ν μ R c r2 g τ (meridPt y) = w2NW ν μ R c r2 g τ y := by
  unfold w2NW
  rw [w10_varrho_meridPt, w10_mp2]

theorem w2NW_measurable {ν μ R c : ℝ} (hν : 0 < ν) (r2 : ℝ) {g : Chart → Ten3}
    (hg : Measurable g) :
    Measurable (fun x : ℝ × Space => w2NW ν μ R c r2 g x.1 x.2) := by
  unfold w2NW
  have hT : ∀ i j, Measurable
      (fun x : ℝ × Space => oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g x.1 x.2 i j) :=
    oldCutMeasurable R c (R * Real.sqrt (5 * ν / 6)) g hg
  have hZ := sepWre_measurable ν μ hν _ hT
  have hO := outPrim_measurable hZ
  have hq : Measurable (fun x : ℝ × Space => ((x.1, ϱ x.2, x.2 2) : ℝ × ℝ × ℝ)) :=
    measurable_fst.prodMk ((continuous_ϱ.measurable.comp measurable_snd).prodMk
      ((EuclideanSpace.proj (2 : Fin 3)).continuous.measurable.comp measurable_snd))
  refine Measurable.ite ?_ (hO.comp hq).abs measurable_const
  exact measurableSet_le (continuous_ϱ.measurable.comp measurable_snd) measurable_const

theorem w2PhiW_norm (ν μ R c r2 : ℝ) (g : Chart → Ten3) (τ : ℝ) (y : Space) :
    ‖w2PhiW ν μ R c r2 g τ y‖ = w2NW ν μ R c r2 g τ y := by
  unfold w2PhiW
  rw [norm_smul, wyl_norm_coordinateVector, mul_one,
    Real.norm_of_nonneg (w2NW_nonneg _ _ _ _ _ _ _ _)]

/-- Domination of the outward primitive of `sepWre ν μ T`. -/
theorem w113_psiW_dom {ν μ R c : ℝ} (hν : 0 < ν) (hR : 0 < R) (hc : 0 < c) (hμ : -(1 / 4) < μ)
    (r2 : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : Chart → Ten3, IsOldL2 c ν g → ∀ (τ : ℝ) (y : Space),
      R * Real.sqrt ν ≤ ϱ y → ϱ y ≤ r2 →
        ENNReal.ofReal
            |outPrim (sepWre ν μ (oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g)) τ (ϱ y) (y 2)| ≤
          ENNReal.ofReal C * w2Dom (w2k (R * Real.sqrt (5 * ν / 6))
            (R * Real.sqrt ν - R * Real.sqrt (5 * ν / 6)) (r2 + R * Real.sqrt (5 * ν / 6)))
            (2 * μ + 2) (IIIa.srcNorm (oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g)) τ y := by
  obtain ⟨C0, hC0, hdom⟩ := w2_wdom
  refine ⟨‖w10Re‖ * C0, by positivity, ?_⟩
  intro g hg τ y hy1 hy2
  obtain ⟨hS, _, _⟩ := w10_ctx hν hR hc hg
  set r0 : ℝ := R * Real.sqrt (5 * ν / 6)
  set T := oldCutSrc R c r0 g
  have hr0nn : 0 ≤ r0 := by positivity
  have hP : 0 < 2 * c / R := by positivity
  have hrr : r0 < R * Real.sqrt ν :=
    mul_lt_mul_of_pos_left (Real.sqrt_lt_sqrt (by positivity) (by linarith)) hR
  set D : ℝ := R * Real.sqrt ν - r0 with hD
  have hDpos : 0 < D := sub_pos.2 hrr
  set a : ℝ := 2 * μ + 2
  set G := IIIa.srcNorm T
  have hpt : ∀ p : Space, R * Real.sqrt ν ≤ ϱ p →
      ENNReal.ofReal |sepWre ν μ T τ p 2| ≤
        ENNReal.ofReal (‖w10Re‖ * C0) * w2Dom (IIIa.sepKd 0 D) a G τ p := by
    intro p hp
    have e1 : |sepWre ν μ T τ p 2| ≤ ‖sepWre ν μ T τ p‖ := wyl_abs_apply_le _ 2
    have d1 := hdom ν hν μ hμ r0 (R * Real.sqrt ν) (2 * c / R) hr0nn hrr hP T hS τ p hp
    have m1 := w2_enorm_sepWre (ν := ν) μ T τ p
    calc ENNReal.ofReal |sepWre ν μ T τ p 2|
        ≤ ENNReal.ofReal ‖sepWre ν μ T τ p‖ := ENNReal.ofReal_le_ofReal e1
      _ = ‖sepWre ν μ T τ p‖ₑ := ofReal_norm (sepWre ν μ T τ p)
      _ ≤ ENNReal.ofReal ‖w10Re‖ * (ENNReal.ofReal C0 * w2Dom (IIIa.sepKd 0 D) a G τ p) :=
          m1.trans (mul_le_mul' le_rfl d1)
      _ = ENNReal.ofReal (‖w10Re‖ * C0) * w2Dom (IIIa.sepKd 0 D) a G τ p := by
          rw [ENNReal.ofReal_mul (norm_nonneg _), mul_assoc]
  have hnorm : ENNReal.ofReal |outPrim (sepWre ν μ T) τ (ϱ y) (y 2)| ≤
      ∫⁻ ρ in Ioi (ϱ y), ‖ρ * sepWre ν μ T τ (!₂[ρ, 0, y 2] : Space) 2‖ₑ := by
    unfold outPrim
    rw [← Real.enorm_eq_ofReal_abs, enorm_neg]
    exact enorm_integral_le_lintegral_enorm _
  refine hnorm.trans ?_
  calc ∫⁻ ρ in Ioi (ϱ y), ‖ρ * sepWre ν μ T τ (!₂[ρ, 0, y 2] : Space) 2‖ₑ
      ≤ ∫⁻ ρ in Ioi (ϱ y), ENNReal.ofReal (‖w10Re‖ * C0) *
          (ENNReal.ofReal ρ * w2Dom (IIIa.sepKd 0 D) a G τ (!₂[ρ, 0, y 2] : Space)) := by
        refine setLIntegral_mono' measurableSet_Ioi fun ρ hρ => ?_
        have hρ' : ϱ y < ρ := hρ
        have hρ0 : 0 ≤ ρ := (ϱ_nonneg y).trans hρ'.le
        have hϱ : ϱ (!₂[ρ, 0, y 2] : Space) = ρ := wardFar_varrho ρ (y 2) hρ0
        have := hpt (!₂[ρ, 0, y 2] : Space) (by rw [hϱ]; linarith)
        rw [enorm_mul, Real.enorm_of_nonneg hρ0, ← ofReal_norm, Real.norm_eq_abs]
        calc ENNReal.ofReal ρ * ENNReal.ofReal |sepWre ν μ T τ (!₂[ρ, 0, y 2] : Space) 2|
            ≤ ENNReal.ofReal ρ * (ENNReal.ofReal (‖w10Re‖ * C0) *
                w2Dom (IIIa.sepKd 0 D) a G τ (!₂[ρ, 0, y 2] : Space)) := by gcongr
          _ = _ := by ring
    _ = ENNReal.ofReal (‖w10Re‖ * C0) *
          ∫⁻ ρ in Ioi (ϱ y), ENNReal.ofReal ρ *
            w2Dom (IIIa.sepKd 0 D) a G τ (!₂[ρ, 0, y 2] : Space) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := by
        gcongr
        exact w2_tonelli hr0nn hDpos a (w2_srcNorm_measurable hS)
          (fun τ' z hz => w2_srcNorm_zero hS τ' hz) τ hy2 (by rw [hD]; linarith)

/-- `WylBd` for the outward primitive of `sepWre ν μ T`. -/
theorem w113_psiWBd {ν μ R c : ℝ} (hν : 0 < ν) (hR : 0 < R) (hc : 0 < c) (hμ : -(1 / 4) < μ)
    (r2 : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ g : Chart → Ten3, IsOldL2 c ν g →
      WylBd (ageμ c (-3 / 2)) (eLpNorm g 2 (ageμ c (-1 / 2)))
        (wardYoungRead ν R (w2PhiW ν μ R c r2 g)) K := by
  obtain ⟨C, hC, hDom⟩ := w113_psiW_dom hν hR hc hμ r2
  obtain ⟨B, hB, hLt⟩ := w2_ltau hν hR hc hμ r2
  refine ⟨C * B, mul_nonneg hC hB, ?_⟩
  intro g hg
  obtain ⟨hS, _, _⟩ := w10_ctx hν hR hc hg
  set r0 : ℝ := R * Real.sqrt (5 * ν / 6) with hr0
  set T := oldCutSrc R c r0 g with hT
  set N : ℝ → Space → ℝ := w2NW ν μ R c r2 g with hN
  have hNm : Measurable (fun x : ℝ × Space => N x.1 x.2) := w2NW_measurable hν r2 hg.measurable
  have hN0 : ∀ τ y, 0 ≤ N τ y := w2NW_nonneg ν μ R c r2 g
  have hNper : ∀ τ y, N (τ + 2 * c / R) y = N τ y := by
    intro τ y
    simp only [hN, w2NW, ← hr0, ← hT, outPrim, sepWre_periodic ν μ _ _ hS.periodic]
  have hFm : Measurable (fun x : ℝ × Space => w2PhiW ν μ R c r2 g x.1 x.2) :=
    hNm.smul_const _
  refine ⟨(w10_read_meas hFm).aestronglyMeasurable, ?_⟩
  have hDom' : ∀ τ y, R * Real.sqrt ν ≤ ϱ y →
      ENNReal.ofReal (N τ (meridPt y)) ≤ ENNReal.ofReal C *
        w2Dom (w2k r0 (R * Real.sqrt ν - r0) (r2 + r0)) (2 * μ + 2) (IIIa.srcNorm T) τ y := by
    intro τ y hy
    rw [hN, w2NW_meridPt]
    unfold w2NW
    split_ifs with h
    · exact hDom g hg τ y hy h
    · simp
  have hTr := chartYoungTransport R c ν hR hc hν (w10Fn R ν N) (w10Fn_measurable R ν hNm)
    (w10Fn_axi R ν N) (w10Fn_periodic R ν _ hNper)
  have hI : ∫⁻ p in {p : Chart | ν * p.1 ≤ 1}, ‖coefOf R (w10Fn R ν N) p‖ₑ ^ (2 : ℝ)
        ∂(ageμ c (-3 / 2)) ≤
      ENNReal.ofReal (1 / (Real.pi * R ^ 2)) *
        (ENNReal.ofReal C * (ENNReal.ofReal B *
          IIIa.ltauLq (2 * c / R) 2 (IIIa.srcNorm T))) ^ (2 : ℝ) := by
    refine hTr.trans ?_
    gcongr
    have hpt : ∀ τ y, (if R * Real.sqrt ν ≤ Real.sqrt (y 0 ^ 2 + y 1 ^ 2) then
        ‖w10Fn R ν N τ y‖ₑ else 0) ≤ ENNReal.ofReal C *
          w2Dom (w2k r0 (R * Real.sqrt ν - r0) (r2 + r0)) (2 * μ + 2) (IIIa.srcNorm T) τ y := by
      intro τ y
      by_cases h : R * Real.sqrt ν ≤ Real.sqrt (y 0 ^ 2 + y 1 ^ 2)
      · rw [if_pos h]
        have h' : R * Real.sqrt ν ≤ ϱ y := h
        rw [w10Fn_enorm hN0 τ h']
        exact hDom' τ y h'
      · rw [if_neg h]
        exact zero_le
    calc IIIa.ltauLq (2 * c / R) 2 (fun τ y => if R * Real.sqrt ν ≤ Real.sqrt (y 0 ^ 2 + y 1 ^ 2)
            then ‖w10Fn R ν N τ y‖ₑ else 0)
        ≤ IIIa.ltauLq (2 * c / R) 2 (fun τ y => ENNReal.ofReal C *
            w2Dom (w2k r0 (R * Real.sqrt ν - r0) (r2 + r0)) (2 * μ + 2) (IIIa.srcNorm T) τ y) :=
          IIIa.ltauLq_mono _ _ (by norm_num) hpt
      _ = ENNReal.ofReal C * IIIa.ltauLq (2 * c / R) 2
            (w2Dom (w2k r0 (R * Real.sqrt ν - r0) (r2 + r0)) (2 * μ + 2) (IIIa.srcNorm T)) :=
          IIIa.ltauLq_const_mul _ _ (by norm_num) _ ENNReal.ofReal_ne_top _
      _ ≤ _ := mul_le_mul_of_nonneg_left (hLt g hg) zero_le
  have hF : ∀ τ y, R * Real.sqrt ν ≤ ϱ y → ‖w2PhiW ν μ R c r2 g τ y‖ ≤ N τ y :=
    fun τ y _ => le_of_eq (w2PhiW_norm ν μ R c r2 g τ y)
  exact w10_final hν hR hc g hg.measurable r0 hN0 hF C B hC hB hI

theorem w113_norm_merid_sepWre {ν μ R c : ℝ} (hν : 0 < ν) (hR : 0 < R) (hc : 0 < c)
    (hμ : -(1 / 4) < μ) {g : Chart → Ten3} (hg : IsOldL2 c ν g) (τ : ℝ) (y : Space)
    (hy : R * Real.sqrt (5 * ν / 6) < ϱ y) :
    ‖sepWre ν μ (oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g) τ (meridPt y)‖ =
      ‖sepWre ν μ (oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g) τ y‖ := by
  obtain ⟨hS, hM, hAx⟩ := w10_ctx hν hR hc hg
  have hr : 0 ≤ R * Real.sqrt (5 * ν / 6) := by positivity
  have hP : 0 < 2 * c / R := by positivity
  have hρ : 0 < ϱ y := lt_of_le_of_lt hr hy
  obtain ⟨M, hMo, hTM, hmer, -⟩ := w10_rotdatum hAx hρ
  have hmU : R * Real.sqrt (5 * ν / 6) < ϱ (meridPt y) := by
    rw [w10_varrho_meridPt]; exact hy
  have e := w10_equivV hν hμ hr hP hS hM hMo hTM τ (meridPt y) hmU
  rw [hmer] at e
  rw [e, norm_actM hMo]

theorem w113_streamCorrW_pd_bound {ν μ R c : ℝ} {χy : ℝ → ℝ} (hχ : IsYoungCutoff χy)
    (hν : 0 < ν) (hR : 0 < R) (hc : 0 < c) (hμ : -(1 / 4) < μ)
    {g : Chart → Ten3} (hg : IsOldL2 c ν g) (τ : ℝ) (j : Fin 3)
    {y : Space} (hy : y ∈ youngOpen ν R) :
    ‖physPd (streamCorr ν R χy (sepWre ν μ (oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g)) τ) j y‖ ≤
      |deriv (w2a ν R χy) (ϱ y)| *
        |outPrim (sepWre ν μ (oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g)) τ (ϱ y) (y 2)| +
        |w2a ν R χy (ϱ y)| *
          (2 * ϱ y * ‖sepWre ν μ (oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g) τ y‖) := by
  obtain ⟨hS, hM, hAx⟩ := w10_ctx hν hR hc hg
  set T := oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g with hTdef
  have hr0 : 0 ≤ R * Real.sqrt (5 * ν / 6) := by positivity
  have hP : 0 < 2 * c / R := by positivity
  have hy' : y ∉ axis := t9_not_axis hν hR hy
  have hρ : 0 < ϱ y := ϱ_pos hy'
  have hΨ : HasFDerivAt (fun x : Space => outPrim (sepWre ν μ T) τ (ϱ x) (x 2))
      ((ϱ y * sepWre ν μ T τ (meridPt y) 2) • ϱD y +
        (-(ϱ y * sepWre ν μ T τ (meridPt y) 0)) •
          (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ)) y :=
    wgx_outPrim_hasFDerivAt hν hR (Sub8_1_1_2_3.wre_contDiffOn hν hμ hr0 hP hS hM τ)
      (fun r z hr => Sub8_1_1_2_3.wre_partials hν hR hμ hP hS hM hAx τ r z hr) hy
  have hwd : HasDerivAt (w2a ν R χy) (deriv (w2a ν R χy) (ϱ y)) (ϱ y) :=
    (((w2a_contDiffOn (ν := ν) (R := R) hχ).contDiffAt (Ioi_mem_nhds hρ)).differentiableAt
      one_ne_zero).hasDerivAt
  have hA := (hwd.comp_hasFDerivAt y (hasFDerivAt_ϱ hy')).mul hΨ
  have hC := hA.smul_const (coordinateVector 2)
  have hfun : streamCorr ν R χy (sepWre ν μ T) τ =
      fun x : Space => ((w2a ν R χy ∘ ϱ) x * outPrim (sepWre ν μ T) τ (ϱ x) (x 2)) •
        coordinateVector 2 := by
    funext x; rfl
  unfold physPd
  rw [hfun]
  have hEq := congrArg (fun L : Space →L[ℝ] Space => ‖L (coordinateVector j)‖) hC.fderiv
  refine le_of_eq_of_le hEq ?_
  simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, norm_smul, wyl_norm_coordinateVector, mul_one,
    Real.norm_eq_abs, Function.comp]
  have hn := w113_norm_merid_sepWre (μ := μ) hν hR hc hμ hg τ y hy
  have hm2 : |sepWre ν μ T τ (meridPt y) 2| ≤ ‖sepWre ν μ T τ y‖ :=
    hn ▸ wyl_abs_apply_le _ 2
  have hm0 : |sepWre ν μ T τ (meridPt y) 0| ≤ ‖sepWre ν μ T τ y‖ :=
    hn ▸ wyl_abs_apply_le _ 0
  have hD := w2_abs_ϱD y hy' j
  have hE := w2_abs_cv2 j
  set Ψ := outPrim (sepWre ν μ T) τ (ϱ y) (y 2)
  set w := w2a ν R χy (ϱ y)
  set w' := deriv (w2a ν R χy) (ϱ y)
  set d := ϱD y (coordinateVector j)
  set e := coordinateVector j 2
  set Z2 := sepWre ν μ T τ (meridPt y) 2
  set Z0 := sepWre ν μ T τ (meridPt y) 0
  set N := ‖sepWre ν μ T τ y‖
  have hPb : |ϱ y * Z2 * d| ≤ ϱ y * N := by
    rw [abs_mul, abs_mul, abs_of_pos hρ]
    calc ϱ y * |Z2| * |d| ≤ ϱ y * N * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hm2 hρ.le) hD (abs_nonneg _) (by positivity)
      _ = ϱ y * N := by ring
  have hQb : |-(ϱ y * Z0) * e| ≤ ϱ y * N := by
    rw [abs_mul, abs_neg, abs_mul, abs_of_pos hρ]
    calc ϱ y * |Z0| * |e| ≤ ϱ y * N * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hm0 hρ.le) hE (abs_nonneg _) (by positivity)
      _ = ϱ y * N := by ring
  have hsum : |ϱ y * Z2 * d + -(ϱ y * Z0) * e| ≤ 2 * ϱ y * N := by
    calc _ ≤ |ϱ y * Z2 * d| + |-(ϱ y * Z0) * e| := abs_add_le _ _
      _ ≤ 2 * ϱ y * N := by linarith
  calc |w * (ϱ y * Z2 * d + -(ϱ y * Z0) * e) + Ψ * (w' * d)|
      ≤ |w * (ϱ y * Z2 * d + -(ϱ y * Z0) * e)| + |Ψ * (w' * d)| := abs_add_le _ _
    _ ≤ |w'| * |Ψ| + |w| * (2 * ϱ y * N) := by
        rw [abs_mul, abs_mul, abs_mul]
        have h1 : |w| * |ϱ y * Z2 * d + -(ϱ y * Z0) * e| ≤ |w| * (2 * ϱ y * N) :=
          mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
        have h2 : |Ψ| * (|w'| * |d|) ≤ |w'| * |Ψ| := by
          calc |Ψ| * (|w'| * |d|) ≤ |Ψ| * (|w'| * 1) :=
                mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_left hD (abs_nonneg _)) (abs_nonneg _)
            _ = |w'| * |Ψ| := by ring
        linarith

theorem w113_streamCorrW_measurable {ν μ R c : ℝ} {χy : ℝ → ℝ} (hν : 0 < ν)
    {g : Chart → Ten3} (hg : IsOldL2 c ν g) :
    Measurable (fun x : ℝ × Space =>
      streamCorr ν R χy (sepWre ν μ (oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g)) x.1 x.2) := by
  have hT : ∀ i j, Measurable
      (fun x : ℝ × Space => oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g x.1 x.2 i j) :=
    oldCutMeasurable R c (R * Real.sqrt (5 * ν / 6)) g hg.measurable
  have hZ := sepWre_measurable ν μ hν _ hT
  have hO := outPrim_measurable hZ
  have hq : Measurable (fun x : ℝ × Space => ((x.1, ϱ x.2, x.2 2) : ℝ × ℝ × ℝ)) :=
    measurable_fst.prodMk ((continuous_ϱ.measurable.comp measurable_snd).prodMk
      ((EuclideanSpace.proj (2 : Fin 3)).continuous.measurable.comp measurable_snd))
  have hw : Measurable (fun x : ℝ × Space => w2a ν R χy (ϱ x.2)) :=
    (w2a_measurable ν R χy).comp (continuous_ϱ.measurable.comp measurable_snd)
  exact (hw.mul (hO.comp hq)).smul measurable_const

theorem w113_streamCorrW_diffAt {ν μ R c : ℝ} {χy : ℝ → ℝ} (hχy : IsYoungCutoff χy)
    (hν : 0 < ν) (hR : 0 < R) (hc : 0 < c) (hμ : -(1 / 4) < μ)
    {g : Chart → Ten3} (hg : IsOldL2 c ν g) (τ : ℝ) {y : Space} (hy : 0 < ϱ y) :
    DifferentiableAt ℝ
      (streamCorr ν R χy (sepWre ν μ (oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g)) τ) y := by
  have hχ : IsStreamCutoff χy := ⟨hχy.smooth, hχy.one, hχy.zero, hχy.range⟩
  obtain ⟨hS, hM, hAx⟩ := w10_ctx hν hR hc hg
  set T := oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g with hTdef
  have hP : 0 < 2 * c / R := by positivity
  have hW := w113_W_eq (μ := μ) hν hR hc hg
  have hcut : DifferentiableAt ℝ (wardStreamCut ν R χy (sepWre ν μ T) τ) y :=
    Sub8_1_1_2_3.cutW_diffAt hχ hν hR hμ hP hS hM hAx τ hy
  have hYW : DifferentiableAt ℝ (fun y' => χy (ν * age R y') • sepWre ν μ T τ y') y := by
    have hfun : wardYoungW ν μ R c χy g τ = fun y' => χy (ν * age R y') • sepWre ν μ T τ y' := by
      funext y'; simp only [wardYoungW, hW, hTdef]
    rw [← hfun]
    exact w113_wardYoungW_diffAt hχy hν hR hc hμ hg τ hy
  have hcorr_eq : streamCorr ν R χy (sepWre ν μ T) τ =
      fun y' => wardStreamCut ν R χy (sepWre ν μ T) τ y' -
        χy (ν * age R y') • sepWre ν μ T τ y' := by
    funext y'; rw [wardStreamCut_eq]; abel
  rw [hcorr_eq]
  exact hcut.sub hYW

/-- **`∂_j(streamCorr (sepWre))` on the young support**. -/
theorem w113_streamCorrW_pd_youngL2 (ν μ R c : ℝ) (χy : ℝ → ℝ) (hχy : IsYoungCutoff χy)
    (hν : 0 < ν) (hR : 0 < R) (hc : 0 < c) (hμ : -(1 / 4) < μ) :
    ∃ C : ℝ, ∀ g : Chart → Ten3, IsOldL2 c ν g → ∀ j : Fin 3,
      YoungL2Le c ν R C
        (fun τ => physPd
          (streamCorr ν R χy (sepWre ν μ (oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g)) τ) j) g := by
  classical
  obtain ⟨C0, hC0, h0⟩ := w10_single0 μ hμ ν R c hν hR hc
  set r2 : ℝ := R * Real.sqrt (5 * ν / 4)
  have hr2nn : 0 ≤ r2 := by positivity
  obtain ⟨K, hK, hΨ⟩ := w113_psiWBd hν hR hc hμ r2
  obtain ⟨Ca, Cb, hCa, hCb, hab⟩ := w2a_bound hχy hν hR
  have hrr : R * Real.sqrt (5 * ν / 6) < R * Real.sqrt ν :=
    mul_lt_mul_of_pos_left (Real.sqrt_lt_sqrt (by positivity) (by linarith)) hR
  have hr0 : 0 ≤ R * Real.sqrt (5 * ν / 6) := by positivity
  set a : ℝ := Cb
  set b : ℝ := 2 * Ca * r2
  have ha : 0 ≤ a := hCb
  have hb : 0 ≤ b := by positivity
  refine ⟨a * K + b * C0, fun g hg j => ?_⟩
  set T := oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g with hTdef
  set U : Set Space := youngOpen ν R
  have hUo : IsOpen U := isOpen_lt continuous_const continuous_ϱ
  have hPd := w10_meas_pd (w113_streamCorrW_measurable (χy := χy) (μ := μ) hν hg)
    hUo.measurableSet
    (fun τ y hy => w113_streamCorrW_diffAt hχy hν hR hc hμ hg τ (lt_of_le_of_lt hr0 hy)) j
  have hread : wardYoungRead ν R
      (fun τ => physPd (streamCorr ν R χy (sepWre ν μ T) τ) j) =
      wardYoungRead ν R (fun τ y => if y ∈ U then
        physPd (streamCorr ν R χy (sepWre ν μ T) τ) j y else 0) := by
    refine w10_read_congr hν hR fun τ y hy => ?_
    have : y ∈ U := lt_of_lt_of_le hrr hy
    simp [this]
  have hFm : AEStronglyMeasurable
      (wardYoungRead ν R (fun τ => physPd (streamCorr ν R χy (sepWre ν μ T) τ) j))
      (ageμ c (-3 / 2)) := by
    rw [hread]
    exact (w10_read_meas hPd).aestronglyMeasurable
  have hΦ : WylBd (ageμ c (-3 / 2)) (eLpNorm g 2 (ageμ c (-1 / 2)))
      (wardYoungRead ν R (w2PhiW ν μ R c r2 g)) K := hΨ g hg
  have h0T : WylBd (ageμ c (-3 / 2)) (eLpNorm g 2 (ageμ c (-1 / 2)))
      (wardYoungRead ν R (sepWre ν μ T)) C0 := h0 g hg
  have hA : WylBd (ageμ c (-3 / 2)) (eLpNorm g 2 (ageμ c (-1 / 2)))
      (wardYoungRead ν R (fun τ y => a • w2PhiW ν μ R c r2 g τ y)) (a * K) := by
    rw [w2_read_smul, abs_of_nonneg ha]
    have := hΦ.const_mul a
    rwa [abs_of_nonneg ha] at this
  have hB : WylBd (ageμ c (-3 / 2)) (eLpNorm g 2 (ageμ c (-1 / 2)))
      (wardYoungRead ν R (fun τ y => b • sepWre ν μ T τ y)) (b * C0) := by
    rw [w2_read_smul, abs_of_nonneg hb]
    have := h0T.const_mul b
    rwa [abs_of_nonneg hb] at this
  refine w10_young_of_sum hFm hA hB (mul_nonneg ha hK) (mul_nonneg hb hC0) le_rfl
    fun q => w10_read_dom hν hR (fun τ y hy => ?_) q
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ha,
    abs_of_nonneg hb, w2PhiW_norm]
  have hyU : y ∈ U := lt_of_lt_of_le hrr hy
  have hbd := w113_streamCorrW_pd_bound hχy hν hR hc hμ hg τ j hyU
  refine hbd.trans ?_
  by_cases h2 : ϱ y ≤ r2
  · have hN : w2NW ν μ R c r2 g τ y = |outPrim (sepWre ν μ T) τ (ϱ y) (y 2)| := by
      unfold w2NW; rw [if_pos h2]
    rw [hN]
    obtain ⟨h1, h1'⟩ := hab (ϱ y) hy h2
    have hZ := norm_nonneg (sepWre ν μ T τ y)
    have hρ : 0 ≤ ϱ y := ϱ_nonneg y
    have e1 : |deriv (w2a ν R χy) (ϱ y)| * |outPrim (sepWre ν μ T) τ (ϱ y) (y 2)| ≤
        Cb * |outPrim (sepWre ν μ T) τ (ϱ y) (y 2)| :=
      mul_le_mul_of_nonneg_right h1' (abs_nonneg _)
    have e2 : |w2a ν R χy (ϱ y)| * (2 * ϱ y * ‖sepWre ν μ T τ y‖) ≤
        (2 * Ca * r2) * ‖sepWre ν μ T τ y‖ := by
      calc _ ≤ Ca * (2 * r2 * ‖sepWre ν μ T τ y‖) :=
            mul_le_mul h1 (by nlinarith) (by positivity) hCa
        _ = _ := by ring
    change _ ≤ Cb * _ + (2 * Ca * r2) * _
    linarith
  · have h2' := not_le.1 h2
    rw [w2a_zero_of_gt hχy hν hR h2', w2a_deriv_zero_of_gt hχy hν hR h2']
    simp only [abs_zero, zero_mul, add_zero]
    have hN0 := w2NW_nonneg ν μ R c r2 g τ y
    have hZ0 := norm_nonneg (sepWre ν μ T τ y)
    have e3 := mul_nonneg ha hN0
    have e4 := mul_nonneg hb hZ0
    linarith

end UnforcedLeray.Short.PartIIIb.Concrete
end
