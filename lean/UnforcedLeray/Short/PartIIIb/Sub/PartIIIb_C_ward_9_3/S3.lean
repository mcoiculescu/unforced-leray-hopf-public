import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_9_3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_9_3.S2
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_2.TransMajChart
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_2.TransMajFacts
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_1.ChartPhysL2
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_1.L1
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_1.L2
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_1.L3
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_1.L5
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_1.L6
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_1.L7
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_2.L1
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_2_3.K3
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_2_3.K4
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.L8_RepairSepBridge
import UnforcedLeray.Short.PartIIIa.Tasks16.DomYoung

/-!
# `PartIII-b:C/ward/9/3/3`: chart `L²` norm of the weighted transition majorant

Source `the November 2 reference manuscript` 2683-2689, 3631-3656.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

private theorem s3_bridge (R c ν : ℝ) (hR : 0 < R) (hc : 0 < c) (hν : 0 < ν)
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


private def tmaW (a ν R : ℝ) (g : ℝ → Space → ℝ≥0∞) (τ : ℝ) (y : Space) : ℝ≥0∞ :=
  (streamAnn ν R).indicator (fun y => IIIa.sepDom a 0 (transGap ν R) g τ y) y

private def tmaD (a ν R : ℝ) (g : ℝ → Space → ℝ≥0∞) (τ : ℝ) (y : Space) : ℝ≥0∞ :=
  (streamAnn ν R).indicator
    (fun y => ENNReal.ofReal (transLen ν R)⁻¹ * IIIa.sepDom a 1 (transGap ν R) g τ y) y

private def tmaS (a ν R : ℝ) (g : ℝ → Space → ℝ≥0∞) (τ : ℝ) (y : Space) : ℝ≥0∞ :=
  (streamAnn ν R).indicator
    (fun y => ENNReal.ofReal ((transLen ν R)⁻¹ ^ 2) * outMaj a (transGap ν R) g τ (ϱ y) (y 2)) y

private theorem tma_split (a ν R : ℝ) (g : ℝ → Space → ℝ≥0∞) (τ : ℝ) (y : Space) :
    transMajA a ν R g τ y = tmaW a ν R g τ y + tmaD a ν R g τ y + tmaS a ν R g τ y := by
  unfold transMajA tmaW tmaD tmaS
  by_cases hy : y ∈ streamAnn ν R <;> simp [Set.indicator, hy]

private theorem tma_facts (a ν R P : ℝ) {T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ}
    (hT : IIIa.IsSepSource P (R * Real.sqrt (5 * ν / 6)) T) (hA : IsAxiSource T) :
    ChartGood P (tmaW a ν R (IIIa.srcNorm T)) ∧ ChartGood P (tmaD a ν R (IIIa.srcNorm T)) ∧
      ChartGood P (tmaS a ν R (IIIa.srcNorm T)) := by
  have hmeas := srcNorm_measurable hT
  have hper : ∀ τ z, IIIa.srcNorm T (τ + P) z = IIIa.srcNorm T τ z := by
    intro τ z; unfold IIIa.srcNorm; rw [hT.periodic]
  have hax : ∀ (j : ℕ) (D : ℝ) τ (y y' : Space), y' 2 = y 2 →
      y' 0 ^ 2 + y' 1 ^ 2 = y 0 ^ 2 + y 1 ^ 2 →
      IIIa.sepDom a j D (IIIa.srcNorm T) τ y' = IIIa.sepDom a j D (IIIa.srcNorm T) τ y := by
    intro j D τ y y' h2 hr
    obtain ⟨co, si, h, hy⟩ := tmf_exists_rot y y' h2 hr
    rw [← hy]
    exact tmf_sepDom_actM (rotM_orth h) a j D _ (fun τ z => tmf_srcNorm_rot hA h τ z) τ y
  refine ⟨?_, ?_, ?_⟩
  · unfold tmaW
    exact tmf_chartGood (f := fun τ y => IIIa.sepDom a 0 (transGap ν R) (IIIa.srcNorm T) τ y)
      (IIIa.sepAE_measurable_sepDom a 0 _ hmeas)
      (fun τ y => tmf_sepDom_periodic a 0 _ P _ hper τ y)
      (fun τ y y' h2 hr => hax 0 _ τ y y' h2 hr)
  · unfold tmaD
    exact tmf_chartGood
      (f := fun τ y => ENNReal.ofReal (transLen ν R)⁻¹ *
        IIIa.sepDom a 1 (transGap ν R) (IIIa.srcNorm T) τ y)
      (measurable_const.mul (IIIa.sepAE_measurable_sepDom a 1 _ hmeas))
      (fun τ y => by simp only [tmf_sepDom_periodic a 1 _ P _ hper τ y])
      (fun τ y y' h2 hr => by simp only [hax 1 _ τ y y' h2 hr])
  · unfold tmaS
    exact tmf_chartGood
      (f := fun τ y => ENNReal.ofReal ((transLen ν R)⁻¹ ^ 2) *
        outMaj a (transGap ν R) (IIIa.srcNorm T) τ (ϱ y) (y 2))
      (measurable_const.mul (tmf_meas_outMaj a _ hmeas))
      (fun τ y => by
        unfold outMaj
        simp only [tmf_sepDom_periodic a 0 _ P _ hper])
      (fun τ y y' h2 hr => by rw [h2, tmf_varrho_eq hr])

private theorem s3_chart_comp (R c : ℝ) (hR : 0 < R) (hc : 0 < c) (G : ℝ → Space → ℝ≥0∞)
    (hG : ChartGood (2 * c / R) G) :
    (∫⁻ p, ENNReal.ofReal p.1⁻¹ * G (NearInst.chartTau R p) (NearInst.chartY R p) ^ (2 : ℝ)
        ∂srcMeasure c) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal R⁻¹ * IIIa.ltauLq (2 * c / R) 2 G := by
  have hL := chartPhysL2 R c hR hc G hG.1 hG.2.1 hG.2.2
  have hsq : ENNReal.ofReal (R⁻¹ ^ 2) * IIIa.ltauLq (2 * c / R) 2 G ^ (2 : ℝ) =
      (ENNReal.ofReal R⁻¹ * IIIa.ltauLq (2 * c / R) 2 G) ^ (2 : ℝ) := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2),
      ENNReal.ofReal_rpow_of_nonneg (inv_nonneg.2 hR.le) (by norm_num : (0 : ℝ) ≤ 2),
      Real.rpow_two]
  calc _ ≤ (ENNReal.ofReal (R⁻¹ ^ 2) * IIIa.ltauLq (2 * c / R) 2 G ^ (2 : ℝ)) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow hL (by norm_num)
    _ = ENNReal.ofReal R⁻¹ * IIIa.ltauLq (2 * c / R) 2 G := by
        rw [hsq, ← ENNReal.rpow_mul]
        norm_num

/-- **Sub 3** (source 2683-2689, 3631-3656, `p = q = 2`, `b = 1`). -/
theorem wardYTransMajChartG_proved : WardYTransMajChartG := by
  intro ν μ R c hν hR hc hμ
  have ha1 : (1 : ℝ) < 2 * μ + 2 := by linarith
  obtain ⟨CY0, hCY0, hY0⟩ := sepDomYoung 0 2 2 1 (1 / 2) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨CY1, hCY1, hY1⟩ := sepDomYoung 1 2 2 1 (1 / 2) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨CO, hCO, hO⟩ := outMajAnnulusL2P2_proved ν R (2 * μ + 2) hν hR ha1
  have hs1 : Real.sqrt (5 / 6 : ℝ) < 1 := by
    have h := Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 5 / 6) (by norm_num : (5 / 6 : ℝ) < 1)
    rwa [Real.sqrt_one] at h
  have ha : 0 < 1 - Real.sqrt (5 / 6 : ℝ) := by linarith
  have hDpos : 0 < transGap ν R := by
    rw [tmc_sqrt_gap]; exact mul_pos ha (mul_pos hR (Real.sqrt_pos.2 hν))
  have hLpos : 0 < transLen ν R := by
    rw [tmc_transLen]; exact mul_pos hR (Real.sqrt_pos.2 hν)
  have hLinv : 0 ≤ (transLen ν R)⁻¹ := inv_nonneg.2 hLpos.le
  have hKW : 0 ≤ CY0 * transGap ν R ^ (-4 - ((0 : ℕ) : ℝ) + 3 / (1 : ℝ)) :=
    mul_nonneg hCY0 (Real.rpow_nonneg hDpos.le _)
  have hKD : 0 ≤ (transLen ν R)⁻¹ *
      (CY1 * transGap ν R ^ (-4 - ((1 : ℕ) : ℝ) + 3 / (1 : ℝ))) :=
    mul_nonneg hLinv (mul_nonneg hCY1 (Real.rpow_nonneg hDpos.le _))
  have hKS : 0 ≤ (transLen ν R)⁻¹ ^ 2 * CO := mul_nonneg (sq_nonneg _) hCO
  refine ⟨CY0 * transGap ν R ^ (-4 - ((0 : ℕ) : ℝ) + 3 / (1 : ℝ)) +
    (transLen ν R)⁻¹ * (CY1 * transGap ν R ^ (-4 - ((1 : ℕ) : ℝ) + 3 / (1 : ℝ))) +
    (transLen ν R)⁻¹ ^ 2 * CO, by positivity, ?_⟩
  intro g hg
  obtain ⟨hS, hAx, -, hB⟩ := s3_bridge R c ν hR hc hν g hg
  set T := oldCutSrc R c (R * Real.sqrt (5 * ν / 6)) g with hTdef
  have hP : 0 < 2 * c / R := div_pos (mul_pos two_pos hc) hR
  set N : ℝ≥0∞ := eLpNorm g 2 (ageμ c (-1 / 2)) with hNdef
  have hgm : Measurable (Function.uncurry (IIIa.srcNorm T)) := srcNorm_measurable hS
  have hgp : ∀ τ z, IIIa.srcNorm T (τ + 2 * c / R) z = IIIa.srcNorm T τ z := by
    intro τ z
    unfold IIIa.srcNorm
    rw [hS.periodic]
  have hgs : ∀ τ z, R * Real.sqrt (5 * ν / 6) < ϱ z → IIIa.srcNorm T τ z = 0 := by
    intro τ z hz
    have h0 : T τ z = 0 := hS.support τ z hz
    unfold IIIa.srcNorm
    rw [h0]
    simp [IIIa.tensorNorm]
  obtain ⟨cgW, cgD, cgS⟩ := tma_facts (2 * μ + 2) ν R (2 * c / R) hS hAx
  -- W part
  have hWb : IIIa.ltauLq (2 * c / R) 2 (tmaW (2 * μ + 2) ν R (IIIa.srcNorm T)) ≤
      ENNReal.ofReal (CY0 * transGap ν R ^ (-4 - ((0 : ℕ) : ℝ) + 3 / (1 : ℝ))) *
        IIIa.ltauLq (2 * c / R) 2 (IIIa.srcNorm T) := by
    have hpt : ∀ τ y, tmaW (2 * μ + 2) ν R (IIIa.srcNorm T) τ y ≤
        IIIa.sepDom (2 * μ + 2) 0 (transGap ν R) (IIIa.srcNorm T) τ y :=
      fun τ y => Set.indicator_le_self' (fun _ _ => zero_le) y
    have h2 := hY0 (2 * μ + 2) (by linarith) (by linarith) (transGap ν R) (2 * c / R) hDpos hP
      (IIIa.srcNorm T) hgm hgp
    exact (IIIa.ltauLq_mono (2 * c / R) 2 (by norm_num) hpt).trans h2
  -- D part
  have hDb : IIIa.ltauLq (2 * c / R) 2 (tmaD (2 * μ + 2) ν R (IIIa.srcNorm T)) ≤
      ENNReal.ofReal ((transLen ν R)⁻¹ *
        (CY1 * transGap ν R ^ (-4 - ((1 : ℕ) : ℝ) + 3 / (1 : ℝ)))) *
        IIIa.ltauLq (2 * c / R) 2 (IIIa.srcNorm T) := by
    have hpt : ∀ τ y, tmaD (2 * μ + 2) ν R (IIIa.srcNorm T) τ y ≤
        ENNReal.ofReal (transLen ν R)⁻¹ *
          IIIa.sepDom (2 * μ + 2) 1 (transGap ν R) (IIIa.srcNorm T) τ y :=
      fun τ y => Set.indicator_le_self' (fun _ _ => zero_le) y
    have hm1 := (IIIa.ltauLq_mono (2 * c / R) 2 (by norm_num) hpt).trans_eq
      (IIIa.ltauLq_const_mul (2 * c / R) 2 (by norm_num) _ ENNReal.ofReal_ne_top _)
    have h2 := hY1 (2 * μ + 2) (by linarith) (by linarith) (transGap ν R) (2 * c / R) hDpos hP
      (IIIa.srcNorm T) hgm hgp
    refine hm1.trans (le_trans (mul_le_mul_of_nonneg_left h2 zero_le) (le_of_eq ?_))
    rw [ENNReal.ofReal_mul hLinv]
    ring
  -- S part
  have hSb : IIIa.ltauLq (2 * c / R) 2 (tmaS (2 * μ + 2) ν R (IIIa.srcNorm T)) ≤
      ENNReal.ofReal ((transLen ν R)⁻¹ ^ 2 * CO) *
        IIIa.ltauLq (2 * c / R) 2 (IIIa.srcNorm T) := by
    have hfun : tmaS (2 * μ + 2) ν R (IIIa.srcNorm T) = fun τ y =>
        ENNReal.ofReal ((transLen ν R)⁻¹ ^ 2) * (streamAnn ν R).indicator
          (fun y => outMaj (2 * μ + 2) (transGap ν R) (IIIa.srcNorm T) τ (ϱ y) (y 2)) y := by
      funext τ y
      unfold tmaS
      by_cases hy : y ∈ streamAnn ν R <;> simp [Set.indicator, hy]
    have hO' := hO (2 * c / R) hP (IIIa.srcNorm T) hgm hgp hgs
    rw [hfun, IIIa.ltauLq_const_mul (2 * c / R) 2 (by norm_num) _ ENNReal.ofReal_ne_top _]
    refine le_trans (mul_le_mul_of_nonneg_left hO' zero_le) (le_of_eq ?_)
    rw [ENNReal.ofReal_mul (sq_nonneg _)]
    ring
  -- chart
  have hA1 := s3_chart_comp R c hR hc _ cgW
  have hA2 := s3_chart_comp R c hR hc _ cgD
  have hA3 := s3_chart_comp R c hR hc _ cgS
  have hmink := tmc_mink c _ _ _ (tmc_meas_comp cgW.1 R) (tmc_meas_comp cgD.1 R)
    (tmc_meas_comp cgS.1 R)
  -- measure conversion
  have hconv : ∀ F : Chart → ℝ≥0∞, ∫⁻ q, F q ∂(ageμ c (-3 / 2)) =
      ENNReal.ofReal (1 / Real.pi) * ∫⁻ q, F q ∂(srcMeasure c) := by
    intro F
    unfold srcMeasure
    rw [lintegral_smul_measure, smul_eq_mul, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), one_div,
      inv_mul_cancel₀ Real.pi_pos.ne', ENNReal.ofReal_one, one_mul]
  have hroot : ENNReal.ofReal (1 / Real.pi) ^ (1 / 2 : ℝ) =
      ENNReal.ofReal (1 / Real.sqrt Real.pi) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
    congr 1
    rw [← Real.sqrt_eq_rpow, one_div, Real.sqrt_inv, one_div]
  simp only [tma_split]
  rw [hconv, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), hroot]
  have hk : ∀ K : ℝ, 0 ≤ K →
      ENNReal.ofReal (1 / Real.sqrt Real.pi) * (ENNReal.ofReal R⁻¹ *
        (ENNReal.ofReal K * (ENNReal.ofReal (Real.sqrt Real.pi * R) * N))) =
        ENNReal.ofReal K * N := by
    intro K hK
    have hsp : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
    have h1 : ENNReal.ofReal (1 / Real.sqrt Real.pi) * ENNReal.ofReal R⁻¹ *
        ENNReal.ofReal (Real.sqrt Real.pi * R) = 1 := by
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      have : 1 / Real.sqrt Real.pi * R⁻¹ * (Real.sqrt Real.pi * R) = 1 := by
        field_simp
      rw [this, ENNReal.ofReal_one]
    calc _ = (ENNReal.ofReal (1 / Real.sqrt Real.pi) * ENNReal.ofReal R⁻¹ *
          ENNReal.ofReal (Real.sqrt Real.pi * R)) * (ENNReal.ofReal K * N) := by ring
      _ = _ := by rw [h1, one_mul]
  have hlift : ∀ (K : ℝ) (G : ℝ → Space → ℝ≥0∞),
      IIIa.ltauLq (2 * c / R) 2 G ≤ ENNReal.ofReal K * IIIa.ltauLq (2 * c / R) 2 (IIIa.srcNorm T) →
      ENNReal.ofReal R⁻¹ * IIIa.ltauLq (2 * c / R) 2 G ≤
        ENNReal.ofReal R⁻¹ * (ENNReal.ofReal K * (ENNReal.ofReal (Real.sqrt Real.pi * R) * N)) :=
    fun K G h => mul_le_mul_of_nonneg_left (h.trans (by gcongr)) zero_le
  have e1 := hlift _ _ hWb
  have e2 := hlift _ _ hDb
  have e3 := hlift _ _ hSb
  calc ENNReal.ofReal (1 / Real.sqrt Real.pi) * _
      ≤ ENNReal.ofReal (1 / Real.sqrt Real.pi) *
        (ENNReal.ofReal R⁻¹ * (ENNReal.ofReal (CY0 * transGap ν R ^ (-4 - ((0 : ℕ) : ℝ) + 3 / (1 : ℝ))) *
          (ENNReal.ofReal (Real.sqrt Real.pi * R) * N)) +
         ENNReal.ofReal R⁻¹ * (ENNReal.ofReal ((transLen ν R)⁻¹ *
          (CY1 * transGap ν R ^ (-4 - ((1 : ℕ) : ℝ) + 3 / (1 : ℝ)))) *
          (ENNReal.ofReal (Real.sqrt Real.pi * R) * N)) +
         ENNReal.ofReal R⁻¹ * (ENNReal.ofReal ((transLen ν R)⁻¹ ^ 2 * CO) *
          (ENNReal.ofReal (Real.sqrt Real.pi * R) * N))) :=
        mul_le_mul_of_nonneg_left (hmink.trans (add_le_add (add_le_add (hA1.trans e1)
          (hA2.trans e2)) (hA3.trans e3))) zero_le
    _ = ENNReal.ofReal (CY0 * transGap ν R ^ (-4 - ((0 : ℕ) : ℝ) + 3 / (1 : ℝ))) * N +
        ENNReal.ofReal ((transLen ν R)⁻¹ *
          (CY1 * transGap ν R ^ (-4 - ((1 : ℕ) : ℝ) + 3 / (1 : ℝ)))) * N +
        ENNReal.ofReal ((transLen ν R)⁻¹ ^ 2 * CO) * N := by
        rw [mul_add, mul_add, hk _ hKW, hk _ hKD, hk _ hKS]
    _ = _ := by
        rw [ENNReal.ofReal_add (add_nonneg hKW hKD) hKS, ENNReal.ofReal_add hKW hKD,
          add_mul, add_mul]

end UnforcedLeray.Short.PartIIIb.Concrete
