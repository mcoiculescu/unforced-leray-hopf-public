import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Continuity.WardE.Defs
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Continuity.WardE.WardDXSubYoungL2
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Continuity.WardE.WardD2XSubYoungL2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_11_3

/-!
# `PartIII-b:C/cont/WE/3`: `WardDYSubYoungL2`
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- **`∂_j(χ_yW_μ) - ∂_j(χ_yW_{μ'})` on the young support**. -/
theorem w113_wardDYWSubYoungL2 (ν R c : ℝ) (χy : ℝ → ℝ) (hχy : IsYoungCutoff χy)
    (hν : 0 < ν) (hR : 0 < R) (hc : 0 < c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (μ μ' : ℝ), 0 ≤ μ → 0 ≤ μ' →
      ∀ g : Chart → Ten3, IsOldL2 c ν g → ∀ j : Fin 3,
        YoungL2Le c ν R (C * |μ - μ'|)
          (fun τ y => physPd (wardYoungW ν μ R c χy g τ) j y -
            physPd (wardYoungW ν μ' R c χy g τ) j y) g := by
  classical
  obtain ⟨C0, hC0, h0⟩ := wSub_single0 ν R c hν hR hc
  obtain ⟨C1, hC1, h1⟩ := wSub_single1 ν R c hν hR hc
  obtain ⟨Kcut, hKcut, hcut_bd⟩ := w3_cut_deriv_bound R ν hχy hR hν
  refine ⟨C1 + Kcut * C0, by positivity, ?_⟩
  intro μ μ' hμ hμ' g hg j
  have hμ_gt : -(1 / 4) < μ := by linarith
  have hμ'_gt : -(1 / 4) < μ' := by linarith
  obtain ⟨hS, hM, _⟩ := w10_ctx hν hR hc hg
  set T := oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g with hTdef
  have hrr : R * Real.sqrt (5 * ν / 6) < R * Real.sqrt ν :=
    mul_lt_mul_of_pos_left (Real.sqrt_lt_sqrt (by positivity) (by linarith)) hR
  have hr0 : 0 ≤ R * Real.sqrt (5 * ν / 6) := by positivity
  have hP : 0 < 2 * c / R := by positivity
  set U : Set Space := youngOpen ν R
  have hUo : IsOpen U := isOpen_lt continuous_const continuous_ϱ
  have hYW_meas : ∀ (m : ℝ), -(1 / 4) < m →
      Measurable fun x : ℝ × Space => wardYoungW ν m R c χy g x.1 x.2 := by
    intro m _
    have hW := w113_W_eq (μ := m) hν hR hc hg
    have hWm : Measurable fun x : ℝ × Space => sepWre ν m T x.1 x.2 :=
      sepWre_measurable ν m hν T (fun a b => hS.measurable a b)
    have hχm : Measurable fun x : ℝ × Space => χy (ν * age R x.2) := by
      have hage : Measurable fun x : ℝ × Space => ν * age R x.2 := by
        unfold age
        exact measurable_const.mul
          (measurable_const.div ((continuous_ϱ.measurable.comp measurable_snd).pow_const 2))
      exact hχy.smooth.continuous.measurable.comp hage
    have hfun : (fun x : ℝ × Space => wardYoungW ν m R c χy g x.1 x.2) =
        fun x => χy (ν * age R x.2) • sepWre ν m T x.1 x.2 := by
      funext x; simp only [wardYoungW, hW, hTdef]
    rw [hfun]
    exact hχm.smul hWm
  have hdYW : ∀ (m : ℝ), -(1 / 4) < m →
      ∀ τ y, y ∈ U → DifferentiableAt ℝ (wardYoungW ν m R c χy g τ) y := by
    intro m hm τ y hy
    have hy0 : 0 < ϱ y := lt_of_le_of_lt hr0 hy
    exact w113_wardYoungW_diffAt hχy hν hR hc hm hg τ hy0
  have hPd1 := w10_meas_pd (hYW_meas μ hμ_gt) hUo.measurableSet (hdYW μ hμ_gt) j
  have hPd2 := w10_meas_pd (hYW_meas μ' hμ'_gt) hUo.measurableSet (hdYW μ' hμ'_gt) j
  have hread : wardYoungRead ν R
      (fun τ y => physPd (wardYoungW ν μ R c χy g τ) j y -
        physPd (wardYoungW ν μ' R c χy g τ) j y) =
      wardYoungRead ν R (fun τ y =>
        (if y ∈ U then physPd (wardYoungW ν μ R c χy g τ) j y else 0) -
          (if y ∈ U then physPd (wardYoungW ν μ' R c χy g τ) j y else 0)) := by
    refine w10_read_congr hν hR fun τ y hy => ?_
    have : y ∈ U := lt_of_lt_of_le hrr hy
    simp [this]
  have hFm : AEStronglyMeasurable
      (wardYoungRead ν R
        (fun τ y => physPd (wardYoungW ν μ R c χy g τ) j y -
          physPd (wardYoungW ν μ' R c χy g τ) j y))
      (ageμ c (-3 / 2)) := by
    rw [hread]
    exact (w10_read_meas (hPd1.sub hPd2)).aestronglyMeasurable
  have hC1_mu : 0 ≤ C1 * |μ - μ'| := mul_nonneg hC1 (abs_nonneg _)
  have hC0_mu : 0 ≤ C0 * |μ - μ'| := mul_nonneg hC0 (abs_nonneg _)
  have hA : WylBd (ageμ c (-3 / 2)) (eLpNorm g 2 (ageμ c (-1 / 2)))
      (wardYoungRead ν R
        (fun τ y => physPd (sepWre ν μ T τ) j y - physPd (sepWre ν μ' T τ) j y))
      (C1 * |μ - μ'|) :=
    h1 μ μ' hμ hμ' g hg j
  have h0T : WylBd (ageμ c (-3 / 2)) (eLpNorm g 2 (ageμ c (-1 / 2)))
      (wardYoungRead ν R (fun τ y => sepWre ν μ T τ y - sepWre ν μ' T τ y))
      (C0 * |μ - μ'|) := h0 μ μ' hμ hμ' g hg
  have hB : WylBd (ageμ c (-3 / 2)) (eLpNorm g 2 (ageμ c (-1 / 2)))
      (wardYoungRead ν R (fun τ y => Kcut • (sepWre ν μ T τ y - sepWre ν μ' T τ y)))
      (Kcut * (C0 * |μ - μ'|)) := by
    rw [w2_read_smul, abs_of_nonneg hKcut]
    have := h0T.const_mul Kcut
    rwa [abs_of_nonneg hKcut] at this
  refine w10_young_of_sum hFm hA hB hC1_mu (mul_nonneg hKcut hC0_mu) (by linarith) ?_
  refine w10_read_dom hν hR fun τ y hy => ?_
  have hyU : y ∈ U := lt_of_lt_of_le hrr hy
  have hy0 : 0 < ϱ y := lt_of_le_of_lt hr0 hyU
  have hcut_d : HasFDerivAt (fun y' : Space => χy (ν * age R y'))
      (deriv χy (ν * age R y) • (ν • ageD R y)) y :=
    w3_cut_hasFDerivAt hχy (Sub8_1_1_2_3.not_axis_of_pos hy0)
  have hpd_eq : ∀ (m : ℝ), -(1 / 4) < m →
      physPd (wardYoungW ν m R c χy g τ) j y =
        χy (ν * age R y) • physPd (sepWre ν m T τ) j y +
          ((deriv χy (ν * age R y) • (ν • ageD R y)) (coordinateVector j)) •
            sepWre ν m T τ y := by
    intro m hm
    have hW := w113_W_eq (μ := m) hν hR hc hg
    have hW_d : DifferentiableAt ℝ (sepWre ν m T τ) y :=
      w10_diffV hν hm hr0 hP hS hM τ hyU
    have hfun : wardYoungW ν m R c χy g τ = fun y' => χy (ν * age R y') • sepWre ν m T τ y' := by
      funext y'; simp only [wardYoungW, hW, hTdef]
    unfold physPd
    rw [hfun]
    exact congrArg (fun L : Space →L[ℝ] Space => L (coordinateVector j))
      (hcut_d.smul hW_d.hasFDerivAt).fderiv
  rw [hpd_eq μ hμ_gt, hpd_eq μ' hμ'_gt]
  have heq : (χy (ν * age R y) • physPd (sepWre ν μ T τ) j y +
        ((deriv χy (ν * age R y) • (ν • ageD R y)) (coordinateVector j)) • sepWre ν μ T τ y) -
      (χy (ν * age R y) • physPd (sepWre ν μ' T τ) j y +
        ((deriv χy (ν * age R y) • (ν • ageD R y)) (coordinateVector j)) • sepWre ν μ' T τ y) =
      χy (ν * age R y) • (physPd (sepWre ν μ T τ) j y - physPd (sepWre ν μ' T τ) j y) +
        ((deriv χy (ν * age R y) • (ν • ageD R y)) (coordinateVector j)) •
          (sepWre ν μ T τ y - sepWre ν μ' T τ y) := by
    rw [smul_sub, smul_sub]
    abel
  rw [heq]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_smul, Real.norm_eq_abs]
    have hχr := hχy.range (ν * age R y)
    rw [abs_of_nonneg hχr.1]
    exact mul_le_of_le_one_left (norm_nonneg _) hχr.2
  · rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hKcut]
    exact mul_le_mul_of_nonneg_right (hcut_bd y j hy) (norm_nonneg _)

/-- **`∂_j(streamCorr (sepWre ν μ)) - ∂_j(streamCorr (sepWre ν μ'))` on the young support**. -/
theorem w113_streamCorrWSub_pd_youngL2 (ν R c : ℝ) (χy : ℝ → ℝ) (hχy : IsYoungCutoff χy)
    (hν : 0 < ν) (hR : 0 < R) (hc : 0 < c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (μ μ' : ℝ), 0 ≤ μ → 0 ≤ μ' →
      ∀ g : Chart → Ten3, IsOldL2 c ν g → ∀ j : Fin 3,
        YoungL2Le c ν R (C * |μ - μ'|)
          (fun τ y =>
            physPd (streamCorr ν R χy (sepWre ν μ (oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g)) τ) j y -
              physPd (streamCorr ν R χy (sepWre ν μ' (oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g)) τ) j y) g := by
  classical
  obtain ⟨C0, hC0, h0⟩ := wSub_single0 ν R c hν hR hc
  set r2 : ℝ := R * Real.sqrt (5 * ν / 4)
  have hr2nn : 0 ≤ r2 := by positivity
  obtain ⟨K, hK, hΨ⟩ := w2_psiWSubBd hν hR hc r2
  obtain ⟨Ca, Cb, hCa, hCb, hab⟩ := w2a_bound hχy hν hR
  have hrr : R * Real.sqrt (5 * ν / 6) < R * Real.sqrt ν :=
    mul_lt_mul_of_pos_left (Real.sqrt_lt_sqrt (by positivity) (by linarith)) hR
  have hr0 : 0 ≤ R * Real.sqrt (5 * ν / 6) := by positivity
  set a : ℝ := Cb
  set b : ℝ := 2 * Ca * r2
  have ha : 0 ≤ a := hCb
  have hb : 0 ≤ b := by positivity
  refine ⟨a * K + b * C0, by positivity, ?_⟩
  intro μ μ' hμ hμ' g hg j
  have hμ_gt : -(1 / 4) < μ := by linarith
  have hμ'_gt : -(1 / 4) < μ' := by linarith
  set T := oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g
  set U : Set Space := youngOpen ν R
  have hUo : IsOpen U := isOpen_lt continuous_const continuous_ϱ
  have hPd1 := w10_meas_pd (w113_streamCorrW_measurable (χy := χy) (μ := μ) hν hg)
    hUo.measurableSet
    (fun τ y hy => w113_streamCorrW_diffAt hχy hν hR hc hμ_gt hg τ (lt_of_le_of_lt hr0 hy)) j
  have hPd2 := w10_meas_pd (w113_streamCorrW_measurable (χy := χy) (μ := μ') hν hg)
    hUo.measurableSet
    (fun τ y hy => w113_streamCorrW_diffAt hχy hν hR hc hμ'_gt hg τ (lt_of_le_of_lt hr0 hy)) j
  have hread : wardYoungRead ν R
      (fun τ y => physPd (streamCorr ν R χy (sepWre ν μ T) τ) j y -
        physPd (streamCorr ν R χy (sepWre ν μ' T) τ) j y) =
      wardYoungRead ν R (fun τ y =>
        (if y ∈ U then physPd (streamCorr ν R χy (sepWre ν μ T) τ) j y else 0) -
          (if y ∈ U then physPd (streamCorr ν R χy (sepWre ν μ' T) τ) j y else 0)) := by
    refine w10_read_congr hν hR fun τ y hy => ?_
    have : y ∈ U := lt_of_lt_of_le hrr hy
    simp [this]
  have hFm : AEStronglyMeasurable
      (wardYoungRead ν R
        (fun τ y => physPd (streamCorr ν R χy (sepWre ν μ T) τ) j y -
          physPd (streamCorr ν R χy (sepWre ν μ' T) τ) j y))
      (ageμ c (-3 / 2)) := by
    rw [hread]
    exact (w10_read_meas (hPd1.sub hPd2)).aestronglyMeasurable
  have hK_mu : 0 ≤ K * |μ - μ'| := mul_nonneg hK (abs_nonneg _)
  have hC0_mu : 0 ≤ C0 * |μ - μ'| := mul_nonneg hC0 (abs_nonneg _)
  have hΦ : WylBd (ageμ c (-3 / 2)) (eLpNorm g 2 (ageμ c (-1 / 2)))
      (wardYoungRead ν R (w2PhiWSub ν μ μ' R c r2 g)) (K * |μ - μ'|) := hΨ μ μ' hμ hμ' g hg
  have h0T : WylBd (ageμ c (-3 / 2)) (eLpNorm g 2 (ageμ c (-1 / 2)))
      (wardYoungRead ν R (fun τ y => sepWre ν μ T τ y - sepWre ν μ' T τ y))
      (C0 * |μ - μ'|) := h0 μ μ' hμ hμ' g hg
  have hA : WylBd (ageμ c (-3 / 2)) (eLpNorm g 2 (ageμ c (-1 / 2)))
      (wardYoungRead ν R (fun τ y => a • w2PhiWSub ν μ μ' R c r2 g τ y))
      (a * (K * |μ - μ'|)) := by
    rw [w2_read_smul, abs_of_nonneg ha]
    have := hΦ.const_mul a
    rwa [abs_of_nonneg ha] at this
  have hB : WylBd (ageμ c (-3 / 2)) (eLpNorm g 2 (ageμ c (-1 / 2)))
      (wardYoungRead ν R (fun τ y => b • (sepWre ν μ T τ y - sepWre ν μ' T τ y)))
      (b * (C0 * |μ - μ'|)) := by
    rw [w2_read_smul, abs_of_nonneg hb]
    have := h0T.const_mul b
    rwa [abs_of_nonneg hb] at this
  refine w10_young_of_sum hFm hA hB (mul_nonneg ha hK_mu) (mul_nonneg hb hC0_mu) (by linarith)
    fun q => w10_read_dom hν hR (fun τ y hy => ?_) q
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ha,
    abs_of_nonneg hb, w2PhiWSub_norm]
  have hyU : y ∈ U := lt_of_lt_of_le hrr hy
  have hbd := w113_streamCorrWSub_pd_bound hχy hν hR hc hμ_gt hμ'_gt hg τ j hyU
  refine hbd.trans ?_
  by_cases h2 : ϱ y ≤ r2
  · have hN : w2NWSub ν μ μ' R c r2 g τ y =
        |outPrim (sepWre ν μ T) τ (ϱ y) (y 2) - outPrim (sepWre ν μ' T) τ (ϱ y) (y 2)| := by
      unfold w2NWSub; rw [if_pos h2]
    rw [hN]
    obtain ⟨h1, h1'⟩ := hab (ϱ y) hy h2
    have hZ := norm_nonneg (sepWre ν μ T τ y - sepWre ν μ' T τ y)
    have hρ : 0 ≤ ϱ y := ϱ_nonneg y
    have e1 : |deriv (w2a ν R χy) (ϱ y)| *
        |outPrim (sepWre ν μ T) τ (ϱ y) (y 2) - outPrim (sepWre ν μ' T) τ (ϱ y) (y 2)| ≤
        Cb * |outPrim (sepWre ν μ T) τ (ϱ y) (y 2) - outPrim (sepWre ν μ' T) τ (ϱ y) (y 2)| :=
      mul_le_mul_of_nonneg_right h1' (abs_nonneg _)
    have e2 : |w2a ν R χy (ϱ y)| * (2 * ϱ y * ‖sepWre ν μ T τ y - sepWre ν μ' T τ y‖) ≤
        (2 * Ca * r2) * ‖sepWre ν μ T τ y - sepWre ν μ' T τ y‖ := by
      calc _ ≤ Ca * (2 * r2 * ‖sepWre ν μ T τ y - sepWre ν μ' T τ y‖) :=
            mul_le_mul h1 (by nlinarith) (by positivity) hCa
        _ = _ := by ring
    change _ ≤ Cb * _ + (2 * Ca * r2) * _
    linarith
  · have h2' := not_le.1 h2
    rw [w2a_zero_of_gt hχy hν hR h2', w2a_deriv_zero_of_gt hχy hν hR h2']
    simp only [abs_zero, zero_mul, add_zero]
    have hN0 := w2NWSub_nonneg ν μ μ' R c r2 g τ y
    have hZ0 := norm_nonneg (sepWre ν μ T τ y - sepWre ν μ' T τ y)
    have e3 := mul_nonneg ha hN0
    have e4 := mul_nonneg hb hZ0
    linarith

/-- Pointwise bound on
`‖physPd (tcComm ν R χy (wardX0 ν μ R c g) τ) j y - physPd (tcComm ν R χy (wardX0 ν μ' R c g) τ) j y‖`
for `R√ν ≤ ϱ y`. -/
theorem w113_tcCommSub_pd_pt_bound {ν μ μ' R c : ℝ} {χy : ℝ → ℝ} (hχy : IsYoungCutoff χy)
    (hν : 0 < ν) (hR : 0 < R) (hc : 0 < c) (hμ : -(1 / 4) < μ) (hμ' : -(1 / 4) < μ')
    {C : ℝ} (hC : 0 ≤ C)
    (hbd : ∀ y : Space, R * Real.sqrt ν ≤ ϱ y →
      |tcA1 ν R χy (ϱ y)| ≤ C ∧
      (∀ j : Fin 3, |w112_sd1 (fun x => tcA1 ν R χy (ϱ x)) j y| ≤ C) ∧
      (∀ k : Fin 3, |tcA2 ν R χy (ϱ y) * radialUnit y k| ≤ C) ∧
      (∀ k j : Fin 3, |w112_sd1 (fun x => tcA2 ν R χy (ϱ x) * radialUnit x k) j y| ≤ C) ∧
      |tcB1 ν R χy (ϱ y)| ≤ C ∧
      (∀ j : Fin 3, |w112_sd1 (fun x => tcB1 ν R χy (ϱ x)) j y| ≤ C) ∧
      |tcB2 ν R χy (ϱ y)| ≤ C ∧
      (∀ j : Fin 3, |w112_sd1 (fun x => tcB2 ν R χy (ϱ x)) j y| ≤ C))
    (hgt : ∀ y : Space, R * Real.sqrt (5 * ν / 4) < ϱ y →
      tcB1 ν R χy (ϱ y) = 0 ∧
      ∀ j : Fin 3, w112_sd1 (fun x => tcB1 ν R χy (ϱ x)) j y = 0)
    {g : Chart → Ten3} (hg : IsOldL2 c ν g) (τ : ℝ) (j : Fin 3)
    {y : Space} (hy : R * Real.sqrt ν ≤ ϱ y) :
    ‖physPd (tcComm ν R χy (wardX0 ν μ R c g) τ) j y -
        physPd (tcComm ν R χy (wardX0 ν μ' R c g) τ) j y‖ ≤
      C * ‖physPd2 (wardX0 ν μ R c g τ) j 0 y - physPd2 (wardX0 ν μ' R c g τ) j 0 y‖ +
      C * ‖physPd2 (wardX0 ν μ R c g τ) j 1 y - physPd2 (wardX0 ν μ' R c g τ) j 1 y‖ +
      (2 * C) * ‖physPd (wardX0 ν μ R c g τ) j y - physPd (wardX0 ν μ' R c g τ) j y‖ +
      C * ‖physPd (wardX0 ν μ R c g τ) 0 y - physPd (wardX0 ν μ' R c g τ) 0 y‖ +
      C * ‖physPd (wardX0 ν μ R c g τ) 1 y - physPd (wardX0 ν μ' R c g τ) 1 y‖ +
      (2 * C + 2 * C * (R * Real.sqrt (5 * ν / 4))) *
        ‖wardX0 ν μ R c g τ y - wardX0 ν μ' R c g τ y‖ +
      C * w2NSub ν μ μ' R c (R * Real.sqrt (5 * ν / 4)) g τ y := by
  set r2 : ℝ := R * Real.sqrt (5 * ν / 4)
  have hrr : R * Real.sqrt (5 * ν / 6) < R * Real.sqrt ν :=
    mul_lt_mul_of_pos_left (Real.sqrt_lt_sqrt (by positivity) (by linarith)) hR
  have hyU : y ∈ youngOpen ν R := lt_of_lt_of_le hrr hy
  have hUo : IsOpen (youngOpen ν R) := isOpen_lt continuous_const continuous_ϱ
  set Z₁ : Space → Space := wardX0 ν μ R c g τ
  set Z₂ : Space → Space := wardX0 ν μ' R c g τ
  set Z : Space → Space := fun x => Z₁ x - Z₂ x
  set Ψ₁ : Space → ℝ := fun x => outPrim (wardX0 ν μ R c g) τ (ϱ x) (x 2)
  set Ψ₂ : Space → ℝ := fun x => outPrim (wardX0 ν μ' R c g) τ (ϱ x) (x 2)
  set Ψ : Space → ℝ := fun x => Ψ₁ x - Ψ₂ x
  set G3 : Space → Space := fun x => Ψ x • (coordinateVector 2 : Space)
  set G4 : Space → Space := fun x => Z x 2 • (coordinateVector 2 : Space)
  set φ1 : Space → ℝ := fun x => tcA1 ν R χy (ϱ x)
  set φ20 : Space → ℝ := fun x => tcA2 ν R χy (ϱ x) * radialUnit x 0
  set φ21 : Space → ℝ := fun x => tcA2 ν R χy (ϱ x) * radialUnit x 1
  set φ3 : Space → ℝ := fun x => tcB1 ν R χy (ϱ x)
  set φ4 : Space → ℝ := fun x => tcB2 ν R χy (ϱ x)
  obtain ⟨hA1c, _, hB1c, hB2c⟩ := w113_tcCoeff_cdOn2 (ν := ν) (R := R) hχy
  have hϱ2 : ContDiffOn ℝ 2 (fun w : Space => ϱ w) (youngOpen ν R) :=
    contDiffOn_ϱ.mono (fun w hw => t9_not_axis hν hR hw)
  have hmaps : MapsTo (fun w : Space => ϱ w) (youngOpen ν R) (Ioi 0) := fun w hw => by
    have hp := t9_thr_pos hν hR
    have hw' : R * Real.sqrt (5 * ν / 6) < ϱ w := hw
    exact lt_trans hp hw'
  have hφ1d : DifferentiableAt ℝ φ1 y :=
    ((hA1c.comp hϱ2 hmaps).contDiffAt (hUo.mem_nhds hyU)).differentiableAt (by norm_num)
  have hφ3d : DifferentiableAt ℝ φ3 y :=
    ((hB1c.comp hϱ2 hmaps).contDiffAt (hUo.mem_nhds hyU)).differentiableAt (by norm_num)
  have hφ4d : DifferentiableAt ℝ φ4 y :=
    ((hB2c.comp hϱ2 hmaps).contDiffAt (hUo.mem_nhds hyU)).differentiableAt (by norm_num)
  have hφ20d : DifferentiableAt ℝ φ20 y :=
    (((w113_tcA2_rad_jet1_bound hχy hν hR 0).1).contDiffAt
      (hUo.mem_nhds hyU)).differentiableAt (by norm_num)
  have hφ21d : DifferentiableAt ℝ φ21 y :=
    (((w113_tcA2_rad_jet1_bound hχy hν hR 1).1).contDiffAt
      (hUo.mem_nhds hyU)).differentiableAt (by norm_num)
  have hZ₁c3 : ContDiffOn ℝ 3 Z₁ (youngOpen ν R) :=
    (w2_smooth hν hR hc hμ hg τ).of_le (WithTop.coe_le_coe.2 le_top)
  have hZ₂c3 : ContDiffOn ℝ 3 Z₂ (youngOpen ν R) :=
    (w2_smooth hν hR hc hμ' hg τ).of_le (WithTop.coe_le_coe.2 le_top)
  have hZ₁c2 : ContDiffOn ℝ 2 Z₁ (youngOpen ν R) := hZ₁c3.of_le (by norm_num)
  have hZ₂c2 : ContDiffOn ℝ 2 Z₂ (youngOpen ν R) := hZ₂c3.of_le (by norm_num)
  have hZc2 : ContDiffOn ℝ 2 Z (youngOpen ν R) := hZ₁c2.sub hZ₂c2
  have hZd : DifferentiableAt ℝ Z y :=
    (hZc2.contDiffAt (hUo.mem_nhds hyU)).differentiableAt (by norm_num)
  have hZc2' : ContDiffOn ℝ ((1 : WithTop ℕ∞) + 1) Z (youngOpen ν R) := hZc2
  have hfZ : ContDiffOn ℝ 1 (fderiv ℝ Z) (youngOpen ν R) :=
    ((contDiffOn_succ_iff_fderiv_of_isOpen hUo).1 hZc2').2.2
  have hZpd_d : ∀ k : Fin 3, DifferentiableAt ℝ (physPd Z k) y := fun k =>
    (((ContinuousLinearMap.apply ℝ Space (coordinateVector k)).contDiff.comp_contDiffOn
      hfZ).contDiffAt (hUo.mem_nhds hyU)).differentiableAt one_ne_zero
  have hΨ₁c2 : ContDiffOn ℝ 2 Ψ₁ (youngOpen ν R) :=
    (xc_outPrim_c3 hν hR hZ₁c3 (w2_hdr hν hR hc hμ hg τ)).of_le (by norm_num)
  have hΨ₂c2 : ContDiffOn ℝ 2 Ψ₂ (youngOpen ν R) :=
    (xc_outPrim_c3 hν hR hZ₂c3 (w2_hdr hν hR hc hμ' hg τ)).of_le (by norm_num)
  have hΨc2 : ContDiffOn ℝ 2 Ψ (youngOpen ν R) := hΨ₁c2.sub hΨ₂c2
  have hG3d : DifferentiableAt ℝ G3 y :=
    ((hΨc2.smul contDiffOn_const).contDiffAt (hUo.mem_nhds hyU)).differentiableAt (by norm_num)
  have hZ2c2 : ContDiffOn ℝ 2 (fun x : Space => Z x 2) (youngOpen ν R) :=
    (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).contDiff.comp_contDiffOn hZc2
  have hG4d : DifferentiableAt ℝ G4 y :=
    ((hZ2c2.smul contDiffOn_const).contDiffAt (hUo.mem_nhds hyU)).differentiableAt (by norm_num)
  have h1d : DifferentiableAt ℝ (fun x => φ1 x • Z x) y := hφ1d.smul hZd
  have h20d : DifferentiableAt ℝ (fun x => φ20 x • physPd Z 0 x) y := hφ20d.smul (hZpd_d 0)
  have h21d : DifferentiableAt ℝ (fun x => φ21 x • physPd Z 1 x) y := hφ21d.smul (hZpd_d 1)
  have h3d : DifferentiableAt ℝ (fun x => φ3 x • G3 x) y := hφ3d.smul hG3d
  have h4d : DifferentiableAt ℝ (fun x => φ4 x • G4 x) y := hφ4d.smul hG4d
  have hχ : IsStreamCutoff χy := ⟨hχy.smooth, hχy.one, hχy.zero, hχy.range⟩
  obtain ⟨hS, hM, hAx⟩ := w10_ctx hν hR hc hg
  have hr0 : 0 ≤ R * Real.sqrt (5 * ν / 6) := by positivity
  have hP : 0 < 2 * c / R := by positivity
  have hy0 : 0 < ϱ y := lt_of_le_of_lt hr0 hyU
  have hd_tc1 : DifferentiableAt ℝ (tcComm ν R χy (wardX0 ν μ R c g) τ) y := by
    rw [w10_X0_eq (μ := μ) hν hR hc hg]
    exact w113_tcComm_diffAt hχ hν hR hμ hP hS hM hAx τ hy0
  have hd_tc2 : DifferentiableAt ℝ (tcComm ν R χy (wardX0 ν μ' R c g) τ) y := by
    rw [w10_X0_eq (μ := μ') hν hR hc hg]
    exact w113_tcComm_diffAt hχ hν hR hμ' hP hS hM hAx τ hy0
  have hev_tc : (fun x => tcComm ν R χy (wardX0 ν μ R c g) τ x -
      tcComm ν R χy (wardX0 ν μ' R c g) τ x) =ᶠ[𝓝 y]
      fun x => (φ1 x • Z x + (φ20 x • physPd Z 0 x + φ21 x • physPd Z 1 x)) +
        (φ3 x • G3 x + φ4 x • G4 x) := by
    filter_upwards [hUo.mem_nhds hyU] with x hx
    rw [w113_tcComm_eq_sum5 ν R χy (wardX0 ν μ R c g) τ x,
      w113_tcComm_eq_sum5 ν R χy (wardX0 ν μ' R c g) τ x,
      w112_physPd_sub_eq hUo hZ₁c2 hZ₂c2 0 hx,
      w112_physPd_sub_eq hUo hZ₁c2 hZ₂c2 1 hx]
    simp only [Z, Z₁, Z₂, G3, G4, Ψ, Ψ₁, Ψ₂, PiLp.sub_apply, sub_smul, smul_sub]
    abel
  have hpd_tc_sub : physPd (tcComm ν R χy (wardX0 ν μ R c g) τ) j y -
      physPd (tcComm ν R χy (wardX0 ν μ' R c g) τ) j y =
      physPd (fun x => (φ1 x • Z x + (φ20 x • physPd Z 0 x + φ21 x • physPd Z 1 x)) +
        (φ3 x • G3 x + φ4 x • G4 x)) j y := by
    change fderiv ℝ (tcComm ν R χy (wardX0 ν μ R c g) τ) y (coordinateVector j) -
        fderiv ℝ (tcComm ν R χy (wardX0 ν μ' R c g) τ) y (coordinateVector j) =
      fderiv ℝ (fun x => (φ1 x • Z x + (φ20 x • physPd Z 0 x + φ21 x • physPd Z 1 x)) +
        (φ3 x • G3 x + φ4 x • G4 x)) y (coordinateVector j)
    rw [hev_tc.symm.fderiv_eq, fderiv_fun_sub hd_tc1 hd_tc2, sub_apply]
  rw [hpd_tc_sub]
  have hadd1 := w113_physPd_add_norm_le (h1d.fun_add (h20d.fun_add h21d)) (h3d.fun_add h4d) j
  have hadd2 := w113_physPd_add_norm_le h1d (h20d.fun_add h21d) j
  have hadd3 := w113_physPd_add_norm_le h20d h21d j
  have hadd4 := w113_physPd_add_norm_le h3d h4d j
  have hs1 := w113_physPd_smul_norm_le hφ1d hZd j
  have hs20 := w113_physPd_smul_norm_le hφ20d (hZpd_d 0) j
  have hs21 := w113_physPd_smul_norm_le hφ21d (hZpd_d 1) j
  have hs3 := w113_physPd_smul_norm_le hφ3d hG3d j
  have hs4 := w113_physPd_smul_norm_le hφ4d hG4d j
  obtain ⟨cA1_0, cA1_1, cA2_0, cA2_1, cB1_0, cB1_1, cB2_0, cB2_1⟩ := hbd y hy
  have hpdZ : ∀ k : Fin 3, physPd Z k y = physPd Z₁ k y - physPd Z₂ k y :=
    fun k => w112_physPd_sub_eq hUo hZ₁c2 hZ₂c2 k hyU
  have hpd2Z : ∀ k : Fin 3, physPd (physPd Z k) j y = physPd2 Z₁ j k y - physPd2 Z₂ j k y :=
    fun k => w112_physPd2_sub_eq hUo hZ₁c2 hZ₂c2 j k hyU
  have b1 : ‖physPd (fun x => φ1 x • Z x) j y‖ ≤
      C * ‖physPd Z₁ j y - physPd Z₂ j y‖ + C * ‖Z y‖ := by
    rw [hpdZ j] at hs1
    exact hs1.trans (add_le_add
      (mul_le_mul_of_nonneg_right cA1_0 (norm_nonneg _))
      (mul_le_mul_of_nonneg_right (cA1_1 j) (norm_nonneg _)))
  have b20 : ‖physPd (fun x => φ20 x • physPd Z 0 x) j y‖ ≤
      C * ‖physPd2 Z₁ j 0 y - physPd2 Z₂ j 0 y‖ + C * ‖physPd Z₁ 0 y - physPd Z₂ 0 y‖ := by
    rw [hpd2Z 0, hpdZ 0] at hs20
    exact hs20.trans (add_le_add
      (mul_le_mul_of_nonneg_right (cA2_0 0) (norm_nonneg _))
      (mul_le_mul_of_nonneg_right (cA2_1 0 j) (norm_nonneg _)))
  have b21 : ‖physPd (fun x => φ21 x • physPd Z 1 x) j y‖ ≤
      C * ‖physPd2 Z₁ j 1 y - physPd2 Z₂ j 1 y‖ + C * ‖physPd Z₁ 1 y - physPd Z₂ 1 y‖ := by
    rw [hpd2Z 1, hpdZ 1] at hs21
    exact hs21.trans (add_le_add
      (mul_le_mul_of_nonneg_right (cA2_0 1) (norm_nonneg _))
      (mul_le_mul_of_nonneg_right (cA2_1 1 j) (norm_nonneg _)))
  obtain ⟨hG3_0, hG3_1, _⟩ := w112_smul_e2_jets hUo hΨc2 hyU
  rw [hG3_0, hG3_1 j] at hs3
  have b3 : ‖physPd (fun x => φ3 x • G3 x) j y‖ ≤
      (2 * C * r2) * ‖Z y‖ + C * w2NSub ν μ μ' R c r2 g τ y := by
    refine hs3.trans ?_
    by_cases hle : ϱ y ≤ r2
    · obtain ⟨_, hψ1, _⟩ := w112_psiSub_jet hν hR hc hμ hμ' hg τ hyU
      have hN : w2NSub ν μ μ' R c r2 g τ y = |Ψ y| := by
        unfold w2NSub Ψ Ψ₁ Ψ₂; simp only [hle, ↓reduceIte]
      rw [hN]
      have hp1 : |w112_sd1 Ψ j y| ≤ 2 * r2 * ‖Z y‖ :=
        (hψ1 j).2.trans (by nlinarith [norm_nonneg (Z y)])
      have m1 : |φ3 y| * |w112_sd1 Ψ j y| ≤ C * (2 * r2 * ‖Z y‖) :=
        mul_le_mul cB1_0 hp1 (abs_nonneg _) hC
      have m2 : |w112_sd1 φ3 j y| * |Ψ y| ≤ C * |Ψ y| :=
        mul_le_mul_of_nonneg_right (cB1_1 j) (abs_nonneg _)
      linarith
    · obtain ⟨hz0, hz1⟩ := hgt y (not_le.1 hle)
      change |tcB1 ν R χy (ϱ y)| * _ + |w112_sd1 (fun x => tcB1 ν R χy (ϱ x)) j y| * _ ≤ _
      rw [hz0, hz1 j]
      simp only [abs_zero, zero_mul, add_zero]
      have hr2nn : 0 ≤ r2 := by positivity
      have hZ0 := norm_nonneg (Z y)
      have hN0 := w2NSub_nonneg ν μ μ' R c r2 g τ y
      positivity
  obtain ⟨hG4_0, hG4_1, _⟩ := w112_smul_e2_jets hUo hZ2c2 hyU
  rw [hG4_0, hG4_1 j] at hs4
  have hsd_Z2 : w112_sd1 (fun x : Space => Z x 2) j y = (physPd Z₁ j y - physPd Z₂ j y) 2 := by
    rw [← hpdZ j]
    unfold w112_sd1 physPd
    have hd : HasFDerivAt (fun x : Space => (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ) (Z x))
        ((EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).comp (fderiv ℝ Z y)) y :=
      (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).hasFDerivAt.comp y hZd.hasFDerivAt
    exact congrArg (fun L : Space →L[ℝ] ℝ => L (coordinateVector j)) hd.fderiv
  have b4 : ‖physPd (fun x => φ4 x • G4 x) j y‖ ≤
      C * ‖physPd Z₁ j y - physPd Z₂ j y‖ + C * ‖Z y‖ := by
    refine hs4.trans ?_
    rw [hsd_Z2]
    have m1 : |φ4 y| * |(physPd Z₁ j y - physPd Z₂ j y) 2| ≤ C * ‖physPd Z₁ j y - physPd Z₂ j y‖ :=
      mul_le_mul cB2_0 (wyl_abs_apply_le _ 2) (abs_nonneg _) hC
    have m2 : |w112_sd1 φ4 j y| * |Z y 2| ≤ C * ‖Z y‖ :=
      mul_le_mul (cB2_1 j) (wyl_abs_apply_le _ 2) (abs_nonneg _) hC
    linarith
  linarith

/-- **`∂_j(tcComm ν R χy (wardX0 ν μ)) - ∂_j(tcComm ν R χy (wardX0 ν μ'))` on the young support**. -/
theorem w113_tcCommSub_pd_youngL2 (ν R c : ℝ) (χy : ℝ → ℝ) (hχy : IsYoungCutoff χy)
    (hν : 0 < ν) (hR : 0 < R) (hc : 0 < c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (μ μ' : ℝ), 0 ≤ μ → 0 ≤ μ' →
      ∀ g : Chart → Ten3, IsOldL2 c ν g → ∀ j : Fin 3,
        YoungL2Le c ν R (C * |μ - μ'|)
          (fun τ y => physPd (tcComm ν R χy (wardX0 ν μ R c g) τ) j y -
            physPd (tcComm ν R χy (wardX0 ν μ' R c g) τ) j y) g := by
  classical
  obtain ⟨CX0, hCX0, hX0⟩ := wSub_wardX0YoungL2 ν R c hν hR hc
  obtain ⟨CD2, hCD2, hD2⟩ := wSub_wardD2X0YoungL2 ν R c hν hR hc
  set r2 : ℝ := R * Real.sqrt (5 * ν / 4)
  have hr2nn : 0 ≤ r2 := by positivity
  obtain ⟨K, hK, hΨ⟩ := w2_psiSubBd hν hR hc r2
  obtain ⟨C, hC, hbd, hgt⟩ := w113_tcCoeff_all_bounds hχy hν hR
  set a1 : ℝ := C
  set a2 : ℝ := C
  set a3 : ℝ := 2 * C
  set a4 : ℝ := C
  set a5 : ℝ := C
  set a6 : ℝ := 2 * C + 2 * C * r2
  set a7 : ℝ := C
  have ha1 : 0 ≤ a1 := hC
  have ha2 : 0 ≤ a2 := hC
  have ha3 : 0 ≤ a3 := by positivity
  have ha4 : 0 ≤ a4 := hC
  have ha5 : 0 ≤ a5 := hC
  have ha6 : 0 ≤ a6 := by positivity
  have ha7 : 0 ≤ a7 := hC
  have hrr : R * Real.sqrt (5 * ν / 6) < R * Real.sqrt ν :=
    mul_lt_mul_of_pos_left (Real.sqrt_lt_sqrt (by positivity) (by linarith)) hR
  have hr0 : 0 ≤ R * Real.sqrt (5 * ν / 6) := by positivity
  have hP : 0 < 2 * c / R := by positivity
  have hUo : IsOpen (youngOpen ν R) := isOpen_lt continuous_const continuous_ϱ
  refine ⟨a1 * CD2 + a2 * CD2 + a3 * CX0 + a4 * CX0 + a5 * CX0 + a6 * CX0 + a7 * K,
    by positivity, ?_⟩
  intro μ μ' hμ hμ' g hg j
  have hμ_gt : -(1 / 4) < μ := by linarith
  have hμ'_gt : -(1 / 4) < μ' := by linarith
  obtain ⟨hX0_val, hX0_pd⟩ := hX0 μ μ' hμ hμ' g hg
  have hCD2_mu : 0 ≤ CD2 * |μ - μ'| := mul_nonneg hCD2 (abs_nonneg _)
  have hCX0_mu : 0 ≤ CX0 * |μ - μ'| := mul_nonneg hCX0 (abs_nonneg _)
  have hK_mu : 0 ≤ K * |μ - μ'| := mul_nonneg hK (abs_nonneg _)
  have b1 : WylBd (ageμ c (-3 / 2)) (eLpNorm g 2 (ageμ c (-1 / 2)))
      (fun q => a1 * wardYoungRead ν R
        (fun τ y => physPd2 (wardX0 ν μ R c g τ) j 0 y - physPd2 (wardX0 ν μ' R c g τ) j 0 y) q)
      (a1 * (CD2 * |μ - μ'|)) := by
    have := (wyl_bd_of_young (hD2 μ μ' hμ hμ' g hg j 0)).const_mul a1
    rwa [abs_of_nonneg ha1, max_eq_left hCD2_mu] at this
  have b2 : WylBd (ageμ c (-3 / 2)) (eLpNorm g 2 (ageμ c (-1 / 2)))
      (fun q => a2 * wardYoungRead ν R
        (fun τ y => physPd2 (wardX0 ν μ R c g τ) j 1 y - physPd2 (wardX0 ν μ' R c g τ) j 1 y) q)
      (a2 * (CD2 * |μ - μ'|)) := by
    have := (wyl_bd_of_young (hD2 μ μ' hμ hμ' g hg j 1)).const_mul a2
    rwa [abs_of_nonneg ha2, max_eq_left hCD2_mu] at this
  have b3 : WylBd (ageμ c (-3 / 2)) (eLpNorm g 2 (ageμ c (-1 / 2)))
      (fun q => a3 * wardYoungRead ν R
        (fun τ y => physPd (wardX0 ν μ R c g τ) j y - physPd (wardX0 ν μ' R c g τ) j y) q)
      (a3 * (CX0 * |μ - μ'|)) := by
    have := (wyl_bd_of_young (hX0_pd j)).const_mul a3
    rwa [abs_of_nonneg ha3, max_eq_left hCX0_mu] at this
  have b4 : WylBd (ageμ c (-3 / 2)) (eLpNorm g 2 (ageμ c (-1 / 2)))
      (fun q => a4 * wardYoungRead ν R
        (fun τ y => physPd (wardX0 ν μ R c g τ) 0 y - physPd (wardX0 ν μ' R c g τ) 0 y) q)
      (a4 * (CX0 * |μ - μ'|)) := by
    have := (wyl_bd_of_young (hX0_pd 0)).const_mul a4
    rwa [abs_of_nonneg ha4, max_eq_left hCX0_mu] at this
  have b5 : WylBd (ageμ c (-3 / 2)) (eLpNorm g 2 (ageμ c (-1 / 2)))
      (fun q => a5 * wardYoungRead ν R
        (fun τ y => physPd (wardX0 ν μ R c g τ) 1 y - physPd (wardX0 ν μ' R c g τ) 1 y) q)
      (a5 * (CX0 * |μ - μ'|)) := by
    have := (wyl_bd_of_young (hX0_pd 1)).const_mul a5
    rwa [abs_of_nonneg ha5, max_eq_left hCX0_mu] at this
  have b6 : WylBd (ageμ c (-3 / 2)) (eLpNorm g 2 (ageμ c (-1 / 2)))
      (fun q => a6 * wardYoungRead ν R
        (fun τ y => wardX0 ν μ R c g τ y - wardX0 ν μ' R c g τ y) q)
      (a6 * (CX0 * |μ - μ'|)) := by
    have := (wyl_bd_of_young hX0_val).const_mul a6
    rwa [abs_of_nonneg ha6, max_eq_left hCX0_mu] at this
  have b7 : WylBd (ageμ c (-3 / 2)) (eLpNorm g 2 (ageμ c (-1 / 2)))
      (fun q => a7 * wardYoungRead ν R (w2PhiSub ν μ μ' R c r2 g) q)
      (a7 * (K * |μ - μ'|)) := by
    simpa [abs_of_nonneg ha7] using (hΨ μ μ' hμ hμ' g hg).const_mul a7
  have hc1 : 0 ≤ a1 * (CD2 * |μ - μ'|) := mul_nonneg ha1 hCD2_mu
  have hc2 : 0 ≤ a2 * (CD2 * |μ - μ'|) := mul_nonneg ha2 hCD2_mu
  have hc3 : 0 ≤ a3 * (CX0 * |μ - μ'|) := mul_nonneg ha3 hCX0_mu
  have hc4 : 0 ≤ a4 * (CX0 * |μ - μ'|) := mul_nonneg ha4 hCX0_mu
  have hc5 : 0 ≤ a5 * (CX0 * |μ - μ'|) := mul_nonneg ha5 hCX0_mu
  have hc6 : 0 ≤ a6 * (CX0 * |μ - μ'|) := mul_nonneg ha6 hCX0_mu
  have hc7 : 0 ≤ a7 * (K * |μ - μ'|) := mul_nonneg ha7 hK_mu
  have b12 := b1.add b2 hc1 hc2
  have b123 := b12.add b3 (by positivity) hc3
  have b1234 := b123.add b4 (by positivity) hc4
  have b12345 := b1234.add b5 (by positivity) hc5
  have b123456 := b12345.add b6 (by positivity) hc6
  have b1234567 := b123456.add b7 (by positivity) hc7
  have hχ : IsStreamCutoff χy := ⟨hχy.smooth, hχy.one, hχy.zero, hχy.range⟩
  obtain ⟨hS, hM, hAx⟩ := w10_ctx hν hR hc hg
  have hd_tc : ∀ (m : ℝ), -(1 / 4) < m → ∀ τ y, y ∈ youngOpen ν R →
      DifferentiableAt ℝ (w113_tcCommU ν R χy (wardX0 ν m R c g) τ) y := by
    intro m hm τ y hy
    have hev : w113_tcCommU ν R χy (wardX0 ν m R c g) τ =ᶠ[𝓝 y]
        tcComm ν R χy (wardX0 ν m R c g) τ :=
      Filter.mem_of_superset (hUo.mem_nhds hy) fun z hz =>
        w113_tcCommU_eq_of_mem (wardX0 ν m R c g) τ hz
    have hy0 : 0 < ϱ y := lt_of_le_of_lt hr0 hy
    have hd : DifferentiableAt ℝ (tcComm ν R χy (wardX0 ν m R c g) τ) y := by
      rw [w10_X0_eq (μ := m) hν hR hc hg]
      exact w113_tcComm_diffAt hχ hν hR hm hP hS hM hAx τ hy0
    exact hd.congr_of_eventuallyEq hev
  have hPdm1 := w10_meas_pd (w113_tcCommU_measurable hχy hν hR hc hμ_gt hg)
    hUo.measurableSet (hd_tc μ hμ_gt) j
  have hPdm2 := w10_meas_pd (w113_tcCommU_measurable hχy hν hR hc hμ'_gt hg)
    hUo.measurableSet (hd_tc μ' hμ'_gt) j
  have hread : wardYoungRead ν R
      (fun τ y => physPd (tcComm ν R χy (wardX0 ν μ R c g) τ) j y -
        physPd (tcComm ν R χy (wardX0 ν μ' R c g) τ) j y) =
      wardYoungRead ν R (fun τ y =>
        (if y ∈ youngOpen ν R then
          physPd (w113_tcCommU ν R χy (wardX0 ν μ R c g) τ) j y else 0) -
        (if y ∈ youngOpen ν R then
          physPd (w113_tcCommU ν R χy (wardX0 ν μ' R c g) τ) j y else 0)) := by
    refine w10_read_congr hν hR fun τ y hy => ?_
    have hyU : y ∈ youngOpen ν R := lt_of_lt_of_le hrr hy
    have hev1 : w113_tcCommU ν R χy (wardX0 ν μ R c g) τ =ᶠ[𝓝 y]
        tcComm ν R χy (wardX0 ν μ R c g) τ :=
      Filter.mem_of_superset (hUo.mem_nhds hyU) fun z hz =>
        w113_tcCommU_eq_of_mem (wardX0 ν μ R c g) τ hz
    have hev2 : w113_tcCommU ν R χy (wardX0 ν μ' R c g) τ =ᶠ[𝓝 y]
        tcComm ν R χy (wardX0 ν μ' R c g) τ :=
      Filter.mem_of_superset (hUo.mem_nhds hyU) fun z hz =>
        w113_tcCommU_eq_of_mem (wardX0 ν μ' R c g) τ hz
    simp only [hyU, ↓reduceIte, physPd, hev1.fderiv_eq, hev2.fderiv_eq]
  have hFm : AEStronglyMeasurable
      (wardYoungRead ν R
        (fun τ y => physPd (tcComm ν R χy (wardX0 ν μ R c g) τ) j y -
          physPd (tcComm ν R χy (wardX0 ν μ' R c g) τ) j y))
      (ageμ c (-3 / 2)) := by
    rw [hread]
    exact (w10_read_meas (hPdm1.sub hPdm2)).aestronglyMeasurable
  refine ⟨hFm, (eLpNorm_mono_real (fun q => ?_)).trans
    (b1234567.2.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal (by linarith)) le_rfl))⟩
  rw [Real.norm_of_nonneg (wyl_youngRead_nonneg _ _ _ q)]
  by_cases hq : ν * q.1 ≤ 1
  · rcases le_or_gt q.1 0 with hs | hs
    · rw [wyl_youngRead_zero_of_nonpos _ hs]
      have r1 := wyl_youngRead_nonneg ν R
        (fun τ y => physPd2 (wardX0 ν μ R c g τ) j 0 y - physPd2 (wardX0 ν μ' R c g τ) j 0 y) q
      have r2' := wyl_youngRead_nonneg ν R
        (fun τ y => physPd2 (wardX0 ν μ R c g τ) j 1 y - physPd2 (wardX0 ν μ' R c g τ) j 1 y) q
      have r3 := wyl_youngRead_nonneg ν R
        (fun τ y => physPd (wardX0 ν μ R c g τ) j y - physPd (wardX0 ν μ' R c g τ) j y) q
      have r4 := wyl_youngRead_nonneg ν R
        (fun τ y => physPd (wardX0 ν μ R c g τ) 0 y - physPd (wardX0 ν μ' R c g τ) 0 y) q
      have r5 := wyl_youngRead_nonneg ν R
        (fun τ y => physPd (wardX0 ν μ R c g τ) 1 y - physPd (wardX0 ν μ' R c g τ) 1 y) q
      have r6 := wyl_youngRead_nonneg ν R
        (fun τ y => wardX0 ν μ R c g τ y - wardX0 ν μ' R c g τ y) q
      have r7 := wyl_youngRead_nonneg ν R (w2PhiSub ν μ μ' R c r2 g) q
      positivity
    · rw [wyl_youngRead_of_young _ hq, wyl_youngRead_of_young _ hq,
        wyl_youngRead_of_young _ hq, wyl_youngRead_of_young _ hq,
        wyl_youngRead_of_young _ hq, wyl_youngRead_of_young _ hq,
        wyl_youngRead_of_young _ hq, wyl_youngRead_of_young _ hq, w2PhiSub_norm]
      set τ := NearInst.chartTau R q
      set y := NearInst.chartY R q
      have hy : R * Real.sqrt ν ≤ ϱ y := wyl_young_ϱ hν hR hs hq
      have hpt := w113_tcCommSub_pd_pt_bound hχy hν hR hc hμ_gt hμ'_gt hC hbd hgt hg τ j hy
      have hinv : 0 ≤ (Real.sqrt q.1)⁻¹ := inv_nonneg.2 (Real.sqrt_nonneg _)
      have hmul := mul_le_mul_of_nonneg_left hpt hinv
      linarith
  · have hqS : q ∉ wardYoungSet ν := hq
    have h0 : wardYoungRead ν R
        (fun τ y => physPd (tcComm ν R χy (wardX0 ν μ R c g) τ) j y -
          physPd (tcComm ν R χy (wardX0 ν μ' R c g) τ) j y) q = 0 := by
      unfold wardYoungRead
      rw [indicator_of_notMem hqS]
    rw [h0]
    have r1 := wyl_youngRead_nonneg ν R
      (fun τ y => physPd2 (wardX0 ν μ R c g τ) j 0 y - physPd2 (wardX0 ν μ' R c g τ) j 0 y) q
    have r2' := wyl_youngRead_nonneg ν R
      (fun τ y => physPd2 (wardX0 ν μ R c g τ) j 1 y - physPd2 (wardX0 ν μ' R c g τ) j 1 y) q
    have r3 := wyl_youngRead_nonneg ν R
      (fun τ y => physPd (wardX0 ν μ R c g τ) j y - physPd (wardX0 ν μ' R c g τ) j y) q
    have r4 := wyl_youngRead_nonneg ν R
      (fun τ y => physPd (wardX0 ν μ R c g τ) 0 y - physPd (wardX0 ν μ' R c g τ) 0 y) q
    have r5 := wyl_youngRead_nonneg ν R
      (fun τ y => physPd (wardX0 ν μ R c g τ) 1 y - physPd (wardX0 ν μ' R c g τ) 1 y) q
    have r6 := wyl_youngRead_nonneg ν R
      (fun τ y => wardX0 ν μ R c g τ y - wardX0 ν μ' R c g τ y) q
    have r7 := wyl_youngRead_nonneg ν R (w2PhiSub ν μ μ' R c r2 g) q
    positivity

/-- **`∂_j transField_μ - ∂_j transField_{μ'}` on the young support**. -/
theorem w113_wardDYTransSubYoungL2 (ν R c : ℝ) (χy : ℝ → ℝ) (hχy : IsYoungCutoff χy)
    (hν : 0 < ν) (hR : 0 < R) (hc : 0 < c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (μ μ' : ℝ), 0 ≤ μ → 0 ≤ μ' →
      ∀ g : Chart → Ten3, IsOldL2 c ν g → ∀ j : Fin 3,
        YoungL2Le c ν R (C * |μ - μ'|)
          (fun τ y => physPd (transField ν μ R c χy g τ) j y -
            physPd (transField ν μ' R c χy g τ) j y) g := by
  classical
  obtain ⟨C1, hC10, hC1⟩ := w113_streamCorrWSub_pd_youngL2 ν R c χy hχy hν hR hc
  obtain ⟨C2, hC20, hC2⟩ := w113_tcCommSub_pd_youngL2 ν R c χy hχy hν hR hc
  refine ⟨C1 + C2, by positivity, ?_⟩
  intro μ μ' hμ hμ' g hg j
  have hμ_gt : -(1 / 4) < μ := by linarith
  have hμ'_gt : -(1 / 4) < μ' := by linarith
  have hχ : IsStreamCutoff χy := ⟨hχy.smooth, hχy.one, hχy.zero, hχy.range⟩
  obtain ⟨hS, hM, hAx⟩ := w10_ctx hν hR hc hg
  set T := oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g
  have hrr : R * Real.sqrt (5 * ν / 6) < R * Real.sqrt ν :=
    mul_lt_mul_of_pos_left (Real.sqrt_lt_sqrt (by positivity) (by linarith)) hR
  have hr0 : 0 ≤ R * Real.sqrt (5 * ν / 6) := by positivity
  have hP : 0 < 2 * c / R := by positivity
  set U : Set Space := youngOpen ν R
  have hUo : IsOpen U := isOpen_lt continuous_const continuous_ϱ
  set F_U : ℝ → ℝ → Space → Space := fun m τ z =>
    streamCorr ν R χy (sepWre ν m T) τ z + w113_tcCommU ν R χy (wardX0 ν m R c g) τ z
  have hFU_meas : ∀ (m : ℝ), -(1 / 4) < m → Measurable (fun x : ℝ × Space => F_U m x.1 x.2) :=
    fun m hm => (w113_streamCorrW_measurable (χy := χy) (μ := m) hν hg).add
      (w113_tcCommU_measurable hχy hν hR hc hm hg)
  have hFU_eq : ∀ (m : ℝ), -(1 / 4) < m → ∀ τ z, z ∈ U → F_U m τ z = transField ν m R c χy g τ z := by
    intro m hm τ z hz
    have hz0 : 0 < ϱ z := lt_of_le_of_lt hr0 hz
    unfold F_U
    rw [w113_tcCommU_eq_of_mem (wardX0 ν m R c g) τ hz, w10_X0_eq (μ := m) hν hR hc hg,
      ← w113_sepComm_eq_tcComm hχ hν hR hm hP hS hM hAx τ hz0,
      ← w113_transField_eq hν hR hc hg τ z]
  have hd_FU : ∀ (m : ℝ), -(1 / 4) < m → ∀ τ y, y ∈ U → DifferentiableAt ℝ (F_U m τ) y := by
    intro m hm τ y hy
    have hev : F_U m τ =ᶠ[𝓝 y] transField ν m R c χy g τ :=
      Filter.mem_of_superset (hUo.mem_nhds hy) (hFU_eq m hm τ)
    exact (w113_transField_diffAt hχy hν hR hc hm hg τ (lt_of_le_of_lt hr0 hy)).congr_of_eventuallyEq hev
  have hPdm1 := w10_meas_pd (hFU_meas μ hμ_gt) hUo.measurableSet (hd_FU μ hμ_gt) j
  have hPdm2 := w10_meas_pd (hFU_meas μ' hμ'_gt) hUo.measurableSet (hd_FU μ' hμ'_gt) j
  have hread : wardYoungRead ν R
      (fun τ y => physPd (transField ν μ R c χy g τ) j y -
        physPd (transField ν μ' R c χy g τ) j y) =
      wardYoungRead ν R (fun τ y =>
        (if y ∈ U then physPd (F_U μ τ) j y else 0) -
          (if y ∈ U then physPd (F_U μ' τ) j y else 0)) := by
    refine w10_read_congr hν hR fun τ y hy => ?_
    have hyU : y ∈ U := lt_of_lt_of_le hrr hy
    have hev1 : F_U μ τ =ᶠ[𝓝 y] transField ν μ R c χy g τ :=
      Filter.mem_of_superset (hUo.mem_nhds hyU) (hFU_eq μ hμ_gt τ)
    have hev2 : F_U μ' τ =ᶠ[𝓝 y] transField ν μ' R c χy g τ :=
      Filter.mem_of_superset (hUo.mem_nhds hyU) (hFU_eq μ' hμ'_gt τ)
    simp only [hyU, ↓reduceIte, physPd, hev1.fderiv_eq, hev2.fderiv_eq]
  have hFm : AEStronglyMeasurable
      (wardYoungRead ν R
        (fun τ y => physPd (transField ν μ R c χy g τ) j y -
          physPd (transField ν μ' R c χy g τ) j y))
      (ageμ c (-3 / 2)) := by
    rw [hread]
    exact (w10_read_meas (hPdm1.sub hPdm2)).aestronglyMeasurable
  have hC1_mu : 0 ≤ C1 * |μ - μ'| := mul_nonneg hC10 (abs_nonneg _)
  have hC2_mu : 0 ≤ C2 * |μ - μ'| := mul_nonneg hC20 (abs_nonneg _)
  have hA : WylBd (ageμ c (-3 / 2)) (eLpNorm g 2 (ageμ c (-1 / 2)))
      (wardYoungRead ν R (fun τ y =>
        physPd (streamCorr ν R χy (sepWre ν μ T) τ) j y -
          physPd (streamCorr ν R χy (sepWre ν μ' T) τ) j y))
      (C1 * |μ - μ'|) := by
    have := wyl_bd_of_young (hC1 μ μ' hμ hμ' g hg j)
    rwa [max_eq_left hC1_mu] at this
  have hB : WylBd (ageμ c (-3 / 2)) (eLpNorm g 2 (ageμ c (-1 / 2)))
      (wardYoungRead ν R (fun τ y =>
        physPd (tcComm ν R χy (wardX0 ν μ R c g) τ) j y -
          physPd (tcComm ν R χy (wardX0 ν μ' R c g) τ) j y))
      (C2 * |μ - μ'|) := by
    have := wyl_bd_of_young (hC2 μ μ' hμ hμ' g hg j)
    rwa [max_eq_left hC2_mu] at this
  refine w10_young_of_sum hFm hA hB hC1_mu hC2_mu (by linarith)
    fun q => w10_read_dom hν hR (fun τ y hy => ?_) q
  have hyU : y ∈ U := lt_of_lt_of_le hrr hy
  have hy0 : 0 < ϱ y := lt_of_le_of_lt hr0 hyU
  have hpd_eq : ∀ (m : ℝ), -(1 / 4) < m →
      physPd (transField ν m R c χy g τ) j y =
        physPd (streamCorr ν R χy (sepWre ν m T) τ) j y +
          physPd (tcComm ν R χy (wardX0 ν m R c g) τ) j y := by
    intro m hm
    have hX0_eq := w10_X0_eq (μ := m) hν hR hc hg
    have hev : transField ν m R c χy g τ =ᶠ[𝓝 y]
        fun z => streamCorr ν R χy (sepWre ν m T) τ z +
          tcComm ν R χy (wardX0 ν m R c g) τ z := by
      filter_upwards [hUo.mem_nhds hyU] with z hz
      have hz0 : 0 < ϱ z := lt_of_le_of_lt hr0 hz
      rw [w113_transField_eq hν hR hc hg τ z,
        w113_sepComm_eq_tcComm hχ hν hR hm hP hS hM hAx τ hz0, hX0_eq]
    have hd1 : DifferentiableAt ℝ (streamCorr ν R χy (sepWre ν m T) τ) y :=
      w113_streamCorrW_diffAt hχy hν hR hc hm hg τ hy0
    have hd2 : DifferentiableAt ℝ (tcComm ν R χy (wardX0 ν m R c g) τ) y := by
      rw [hX0_eq]
      exact w113_tcComm_diffAt hχ hν hR hm hP hS hM hAx τ hy0
    unfold physPd
    rw [hev.fderiv_eq, fderiv_fun_add hd1 hd2, add_apply]
  rw [hpd_eq μ hμ_gt, hpd_eq μ' hμ'_gt]
  have heq : (physPd (streamCorr ν R χy (sepWre ν μ T) τ) j y +
        physPd (tcComm ν R χy (wardX0 ν μ R c g) τ) j y) -
      (physPd (streamCorr ν R χy (sepWre ν μ' T) τ) j y +
        physPd (tcComm ν R χy (wardX0 ν μ' R c g) τ) j y) =
      (physPd (streamCorr ν R χy (sepWre ν μ T) τ) j y -
        physPd (streamCorr ν R χy (sepWre ν μ' T) τ) j y) +
      (physPd (tcComm ν R χy (wardX0 ν μ R c g) τ) j y -
        physPd (tcComm ν R χy (wardX0 ν μ' R c g) τ) j y) := by
    abel
  rw [heq]
  exact norm_add_le _ _

/-- **Measurability** of the young reading of `∂_jY_μ - ∂_jY_{μ'}` for `ageμ c (-3/2)`. -/
theorem w113_wardDYSubYoungMeas (ν μ μ' R c : ℝ) (χy : ℝ → ℝ) (hχy : IsYoungCutoff χy)
    (hν : 0 < ν) (hR : 0 < R) (hc : 0 < c) (hμ : -(1 / 4) < μ) (hμ' : -(1 / 4) < μ')
    (g : Chart → Ten3) (hg : IsOldL2 c ν g) (j : Fin 3) :
    AEStronglyMeasurable
      (wardYoungRead ν R
        (fun τ y => physPd (wardY ν μ R c χy g τ) j y - physPd (wardY ν μ' R c χy g τ) j y))
      (ageμ c (-3 / 2)) := by
  classical
  have hχ : IsStreamCutoff χy := ⟨hχy.smooth, hχy.one, hχy.zero, hχy.range⟩
  obtain ⟨hS, _, hAx⟩ := w10_ctx hν hR hc hg
  set T := oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g with hTdef
  have hrr : R * Real.sqrt (5 * ν / 6) < R * Real.sqrt ν :=
    mul_lt_mul_of_pos_left (Real.sqrt_lt_sqrt (by positivity) (by linarith)) hR
  have hr0 : 0 ≤ R * Real.sqrt (5 * ν / 6) := by positivity
  have hP : 0 < 2 * c / R := by positivity
  set U : Set Space := youngOpen ν R
  have hUo : IsOpen U := isOpen_lt continuous_const continuous_ϱ
  set Y_U : ℝ → ℝ → Space → Space := fun m τ z =>
    wardYoungW ν m R c χy g τ z +
      (streamCorr ν R χy (sepWre ν m T) τ z + w113_tcCommU ν R χy (wardX0 ν m R c g) τ z)
  have hYU_meas : ∀ (m : ℝ), -(1 / 4) < m → Measurable (fun x : ℝ × Space => Y_U m x.1 x.2) := by
    intro m hm
    have hW := w113_W_eq (μ := m) hν hR hc hg
    have hYW_meas : Measurable fun x : ℝ × Space => wardYoungW ν m R c χy g x.1 x.2 := by
      have hWm : Measurable fun x : ℝ × Space => sepWre ν m T x.1 x.2 :=
        sepWre_measurable ν m hν T (fun a b => hS.measurable a b)
      have hχm : Measurable fun x : ℝ × Space => χy (ν * age R x.2) := by
        have hage : Measurable fun x : ℝ × Space => ν * age R x.2 := by
          unfold age
          exact measurable_const.mul
            (measurable_const.div ((continuous_ϱ.measurable.comp measurable_snd).pow_const 2))
        exact hχy.smooth.continuous.measurable.comp hage
      have hfun : (fun x : ℝ × Space => wardYoungW ν m R c χy g x.1 x.2) =
          fun x => χy (ν * age R x.2) • sepWre ν m T x.1 x.2 := by
        funext x; simp only [wardYoungW, hW, hTdef]
      rw [hfun]
      exact hχm.smul hWm
    exact hYW_meas.add ((w113_streamCorrW_measurable (χy := χy) (μ := m) hν hg).add
      (w113_tcCommU_measurable hχy hν hR hc hm hg))
  have hYU_eq : ∀ (m : ℝ), -(1 / 4) < m → ∀ τ z, z ∈ U → Y_U m τ z = wardY ν m R c χy g τ z := by
    intro m hm τ z hz
    have hres : ShiftedResolventYoung ν m R c g :=
      wardYShiftedRes_proved ν m R c g hν hR hc hm hg
    have hz0 : 0 < ϱ z := lt_of_le_of_lt hr0 hz
    unfold Y_U
    rw [w113_tcCommU_eq_of_mem (wardX0 ν m R c g) τ hz, w10_X0_eq (μ := m) hν hR hc hg,
      ← w113_sepComm_eq_tcComm hχ hν hR hm hP hS (w10_ctx hν hR hc hg).2.1 hAx τ hz0,
      ← w113_transField_eq hν hR hc hg τ z,
      ← wardY_split hχ hν.le hres τ hz0]
  have hd_YU : ∀ (m : ℝ), -(1 / 4) < m → ∀ τ y, y ∈ U → DifferentiableAt ℝ (Y_U m τ) y := by
    intro m hm τ y hy
    have hres : ShiftedResolventYoung ν m R c g :=
      wardYShiftedRes_proved ν m R c g hν hR hc hm hg
    have hy0 : 0 < ϱ y := lt_of_le_of_lt hr0 hy
    have hev : Y_U m τ =ᶠ[𝓝 y]
        fun z => wardYoungW ν m R c χy g τ z + transField ν m R c χy g τ z := by
      filter_upwards [hUo.mem_nhds hy] with z hz
      have hz0 : 0 < ϱ z := lt_of_le_of_lt hr0 hz
      rw [hYU_eq m hm τ z hz, wardY_split hχ hν.le hres τ hz0]
    exact ((w113_wardYoungW_diffAt hχy hν hR hc hm hg τ hy0).add
      (w113_transField_diffAt hχy hν hR hc hm hg τ hy0)).congr_of_eventuallyEq hev
  have hPdm1 := w10_meas_pd (hYU_meas μ hμ) hUo.measurableSet (hd_YU μ hμ) j
  have hPdm2 := w10_meas_pd (hYU_meas μ' hμ') hUo.measurableSet (hd_YU μ' hμ') j
  have hread : wardYoungRead ν R
      (fun τ y => physPd (wardY ν μ R c χy g τ) j y - physPd (wardY ν μ' R c χy g τ) j y) =
      wardYoungRead ν R (fun τ y =>
        (if y ∈ U then physPd (Y_U μ τ) j y else 0) -
          (if y ∈ U then physPd (Y_U μ' τ) j y else 0)) := by
    refine w10_read_congr hν hR fun τ y hy => ?_
    have hyU : y ∈ U := lt_of_lt_of_le hrr hy
    have hev1 : Y_U μ τ =ᶠ[𝓝 y] wardY ν μ R c χy g τ :=
      Filter.mem_of_superset (hUo.mem_nhds hyU) (hYU_eq μ hμ τ)
    have hev2 : Y_U μ' τ =ᶠ[𝓝 y] wardY ν μ' R c χy g τ :=
      Filter.mem_of_superset (hUo.mem_nhds hyU) (hYU_eq μ' hμ' τ)
    simp only [hyU, ↓reduceIte, physPd, hev1.fderiv_eq, hev2.fderiv_eq]
  rw [hread]
  exact (w10_read_meas (hPdm1.sub hPdm2)).aestronglyMeasurable

theorem wdySub_read_le {ν μ μ' R c : ℝ} {χy : ℝ → ℝ} (hχy : IsYoungCutoff χy) (hν : 0 < ν)
    (hR : 0 < R) (g : Chart → Ten3) (hg : IsOldL2 c ν g)
    (hres : ShiftedResolventYoung ν μ R c g) (hres' : ShiftedResolventYoung ν μ' R c g)
    (hc : 0 < c) (hμ : -(1 / 4) < μ) (hμ' : -(1 / 4) < μ') (j : Fin 3) (q : Chart) :
    wardYoungRead ν R
      (fun τ y => physPd (wardY ν μ R c χy g τ) j y - physPd (wardY ν μ' R c χy g τ) j y) q ≤
      wardYoungRead ν R
        (fun τ y => physPd (wardYoungW ν μ R c χy g τ) j y -
          physPd (wardYoungW ν μ' R c χy g τ) j y) q +
      wardYoungRead ν R
        (fun τ y => physPd (transField ν μ R c χy g τ) j y -
          physPd (transField ν μ' R c χy g τ) j y) q := by
  have hχ : IsStreamCutoff χy := ⟨hχy.smooth, hχy.one, hχy.zero, hχy.range⟩
  unfold wardYoungRead
  by_cases hq : q ∈ wardYoungSet ν
  · rw [indicator_of_mem hq, indicator_of_mem hq, indicator_of_mem hq]
    simp only
    by_cases hs : 0 < q.1
    · have hϱ : 0 < ϱ (NearInst.chartY R q) := by
        rw [wyl_ϱ_chartY hR hs]
        exact div_pos hR (Real.sqrt_pos.mpr hs)
      set τ := NearInst.chartTau R q
      set y := NearInst.chartY R q
      have hpd_split : ∀ (m : ℝ) (hm : -(1 / 4) < m) (hr : ShiftedResolventYoung ν m R c g),
          physPd (wardY ν m R c χy g τ) j y =
            physPd (wardYoungW ν m R c χy g τ) j y + physPd (transField ν m R c χy g τ) j y := by
        intro m hm hr
        have hev : wardY ν m R c χy g τ =ᶠ[𝓝 y]
            (wardYoungW ν m R c χy g τ + transField ν m R c χy g τ) := by
          filter_upwards [(isOpen_lt continuous_const continuous_ϱ).mem_nhds hϱ] with z hz
          exact wardY_split hχ hν.le hr τ hz
        obtain ⟨h1, h2⟩ := wardDYRegular_proved ν m R c χy hχy hν hR hc hm g hg τ y hϱ
        unfold physPd
        rw [hev.fderiv_eq, fderiv_add h1 h2]
        rfl
      rw [hpd_split μ hμ hres, hpd_split μ' hμ' hres', ← mul_add]
      refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 (Real.sqrt_nonneg _))
      have heq : (physPd (wardYoungW ν μ R c χy g τ) j y + physPd (transField ν μ R c χy g τ) j y) -
          (physPd (wardYoungW ν μ' R c χy g τ) j y + physPd (transField ν μ' R c χy g τ) j y) =
          (physPd (wardYoungW ν μ R c χy g τ) j y - physPd (wardYoungW ν μ' R c χy g τ) j y) +
            (physPd (transField ν μ R c χy g τ) j y - physPd (transField ν μ' R c χy g τ) j y) := by
        abel
      rw [heq]
      exact norm_add_le _ _
    · have h0 : Real.sqrt q.1 = 0 := Real.sqrt_eq_zero'.2 (not_lt.1 hs)
      simp [h0]
  · rw [indicator_of_notMem hq, indicator_of_notMem hq, indicator_of_notMem hq]
    simp

/-- **`∂_kY_μ - ∂_kY_{μ'} ∈ Y₂` on the young support** (`PartIII-b:C/cont/WE/3`). -/
theorem wardDYSubYoungL2_proved : WardDYSubYoungL2 := by
  intro a b ν R c χy ha _ hχy hν hR hc
  obtain ⟨C1, hC10, hW⟩ := w113_wardDYWSubYoungL2 ν R c χy hχy hν hR hc
  obtain ⟨C2, hC20, hT⟩ := w113_wardDYTransSubYoungL2 ν R c χy hχy hν hR hc
  refine ⟨C1 + C2, fun μ hμ_ab μ' hμ'_ab g hg k => ?_⟩
  have hμ : 0 ≤ μ := by linarith [hμ_ab.1]
  have hμ' : 0 ≤ μ' := by linarith [hμ'_ab.1]
  have hμ_gt : -(1 / 4) < μ := by linarith
  have hμ'_gt : -(1 / 4) < μ' := by linarith
  obtain ⟨hW1, hW2⟩ := hW μ μ' hμ hμ' g hg k
  obtain ⟨hT1, hT2⟩ := hT μ μ' hμ hμ' g hg k
  have hres : ShiftedResolventYoung ν μ R c g :=
    wardYShiftedRes_proved ν μ R c g hν hR hc hμ_gt hg
  have hres' : ShiftedResolventYoung ν μ' R c g :=
    wardYShiftedRes_proved ν μ' R c g hν hR hc hμ'_gt hg
  refine ⟨w113_wardDYSubYoungMeas ν μ μ' R c χy hχy hν hR hc hμ_gt hμ'_gt g hg k, ?_⟩
  have hle : eLpNorm
      (wardYoungRead ν R
        (fun τ y => physPd (wardY ν μ R c χy g τ) k y - physPd (wardY ν μ' R c χy g τ) k y)) 2
      (ageμ c (-3 / 2)) ≤
      eLpNorm (fun q =>
        wardYoungRead ν R
          (fun τ y => physPd (wardYoungW ν μ R c χy g τ) k y -
            physPd (wardYoungW ν μ' R c χy g τ) k y) q +
        wardYoungRead ν R
          (fun τ y => physPd (transField ν μ R c χy g τ) k y -
            physPd (transField ν μ' R c χy g τ) k y) q) 2
      (ageμ c (-3 / 2)) := by
    refine eLpNorm_mono_real (fun q => ?_)
    rw [Real.norm_of_nonneg (wyl_youngRead_nonneg ν R _ q)]
    exact wdySub_read_le hχy hν hR g hg hres hres' hc hμ_gt hμ'_gt k q
  refine le_trans hle (le_trans (eLpNorm_add_le hW1 hT1 (by norm_num : (1 : ENNReal) ≤ 2)) ?_)
  have hC1_mu : 0 ≤ C1 * |μ - μ'| := mul_nonneg hC10 (abs_nonneg _)
  have hC2_mu : 0 ≤ C2 * |μ - μ'| := mul_nonneg hC20 (abs_nonneg _)
  calc _ ≤ ENNReal.ofReal (C1 * |μ - μ'|) * eLpNorm g 2 (ageμ c (-1 / 2)) +
        ENNReal.ofReal (C2 * |μ - μ'|) * eLpNorm g 2 (ageμ c (-1 / 2)) := add_le_add hW2 hT2
    _ = ENNReal.ofReal ((C1 + C2) * |μ - μ'|) * eLpNorm g 2 (ageμ c (-1 / 2)) := by
        rw [show (C1 + C2) * |μ - μ'| = C1 * |μ - μ'| + C2 * |μ - μ'| by ring,
          ENNReal.ofReal_add hC1_mu hC2_mu, add_mul]

end UnforcedLeray.Short.PartIIIb.Concrete
end
