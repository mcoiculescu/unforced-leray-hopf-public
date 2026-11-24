import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_2TransOrg
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_2.TransMajFacts
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_1.ChartPhysL2
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_2.OutMajAnnulusL2
import UnforcedLeray.Short.PartIIIa.Tasks16.DomYoung

/-!
# `PartIII-b:C/rep/5/2/2/2` : `transMajChart`

Source `the November 2 reference manuscript` 2683-2689 (chart normalization),
3631-3656 (`sep:young`, `sep:repair-energy`), 4181-4192 and 5590-5592 (outward stream primitive).
Composition only: Minkowski on the chart for the three components of `transMaj`; for each
component `ChartPhysL2` (with `R = ε⁻¹`, period `2c/R = 2εc`); then `IIIa.SepDomYoung`
(`p = 22/19`, `q = 2`, `b = 11/7`, `δ = 13/22`, `a = 0`) for the `W` and `D` parts, and
`OutMajAnnulusL2` for the `S` part. The real bookkeeping uses `L = R√ν`, `D = (1-√(5/6))L`,
so every component is `ε·(·) ≤ C ε^{34/11} ν⁻³`.
-/

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal
open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-! ## 1. Measurability of the chart maps -/

theorem tmc_meas_chartTau (R : ℝ) : Measurable (fun p : Chart => NearInst.chartTau R p) := by
  unfold NearInst.chartTau
  fun_prop

theorem tmc_meas_chartY (R : ℝ) : Measurable (fun p : Chart => NearInst.chartY R p) := by
  have hv : Measurable fun p : Chart =>
      (![R / Real.sqrt p.1, 0, p.2.2 / Real.sqrt p.1] : Fin 3 → ℝ) := by
    refine measurable_pi_lambda _ fun i => ?_
    fin_cases i <;> simp <;> fun_prop
  exact (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).measurable.comp hv

theorem tmc_meas_comp {G : ℝ → Space → ℝ≥0∞} (hG : Measurable (Function.uncurry G)) (R : ℝ) :
    Measurable (fun p : Chart => G (NearInst.chartTau R p) (NearInst.chartY R p)) :=
  hG.comp ((tmc_meas_chartTau R).prodMk (tmc_meas_chartY R))

/-! ## 2. Minkowski on the chart with the weight `R⁻¹`-free density `p.1⁻¹` -/

theorem tmc_mink (c : ℝ) (f g h : Chart → ℝ≥0∞) (hf : Measurable f) (hg : Measurable g)
    (hh : Measurable h) :
    (∫⁻ p, ENNReal.ofReal p.1⁻¹ * (f p + g p + h p) ^ (2 : ℝ) ∂srcMeasure c) ^ (1 / 2 : ℝ) ≤
      (∫⁻ p, ENNReal.ofReal p.1⁻¹ * f p ^ (2 : ℝ) ∂srcMeasure c) ^ (1 / 2 : ℝ) +
      (∫⁻ p, ENNReal.ofReal p.1⁻¹ * g p ^ (2 : ℝ) ∂srcMeasure c) ^ (1 / 2 : ℝ) +
      (∫⁻ p, ENNReal.ofReal p.1⁻¹ * h p ^ (2 : ℝ) ∂srcMeasure c) ^ (1 / 2 : ℝ) := by
  have hd : Measurable (fun p : Chart => ENNReal.ofReal p.1⁻¹) :=
    ENNReal.measurable_ofReal.comp (measurable_fst.inv)
  have key : ∀ F : Chart → ℝ≥0∞, Measurable F →
      ∫⁻ p, ENNReal.ofReal p.1⁻¹ * F p ∂(srcMeasure c) =
        ∫⁻ p, F p ∂((srcMeasure c).withDensity (fun p : Chart => ENNReal.ofReal p.1⁻¹)) := by
    intro F hF
    exact (lintegral_withDensity_eq_lintegral_mul (srcMeasure c) hd hF).symm
  have hF0 : Measurable (fun p : Chart => (f p + g p + h p) ^ (2 : ℝ)) :=
    (((hf.add hg).add hh)).pow_const _
  have hF1 : Measurable (fun p : Chart => f p ^ (2 : ℝ)) := hf.pow_const _
  have hF2 : Measurable (fun p : Chart => g p ^ (2 : ℝ)) := hg.pow_const _
  have hF3 : Measurable (fun p : Chart => h p ^ (2 : ℝ)) := hh.pow_const _
  rw [key _ hF0, key _ hF1, key _ hF2, key _ hF3]
  have hfg : AEMeasurable (fun p => f p + g p) ((srcMeasure c).withDensity
      (fun p : Chart => ENNReal.ofReal p.1⁻¹)) := (hf.add hg).aemeasurable
  have m1 := ENNReal.lintegral_Lp_add_le (μ := (srcMeasure c).withDensity
      (fun p : Chart => ENNReal.ofReal p.1⁻¹)) (p := 2) (f := fun p => f p + g p) (g := h)
      hfg hh.aemeasurable (by norm_num)
  have m2 := ENNReal.lintegral_Lp_add_le (μ := (srcMeasure c).withDensity
      (fun p : Chart => ENNReal.ofReal p.1⁻¹)) (p := 2) (f := f) (g := g)
      hf.aemeasurable hg.aemeasurable (by norm_num)
  refine le_trans m1 ?_
  exact add_le_add m2 le_rfl

/-! ## 3. One component on the chart -/

theorem tmc_chart_comp (ε c : ℝ) (hε : 0 < ε) (hc : 0 < c) (G : ℝ → Space → ℝ≥0∞)
    (hG : ChartGood (2 * ε * c) G) :
    (∫⁻ p, ENNReal.ofReal p.1⁻¹ * G (NearInst.chartTau ε⁻¹ p) (NearInst.chartY ε⁻¹ p) ^ (2 : ℝ)
        ∂srcMeasure c) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal ε * IIIa.ltauLq (2 * ε * c) 2 G := by
  have hR : (0 : ℝ) < ε⁻¹ := inv_pos.2 hε
  have hPe : 2 * c / ε⁻¹ = 2 * ε * c := by
    rw [div_inv_eq_mul]; ring
  have hper : ∀ τ y, G (τ + 2 * c / ε⁻¹) y = G τ y := by
    intro τ y
    rw [hPe]
    exact hG.2.1 τ y
  have hL := chartPhysL2 ε⁻¹ c hR hc G hG.1 hper hG.2.2
  rw [hPe, inv_inv] at hL
  have hsq : ENNReal.ofReal (ε ^ 2) * IIIa.ltauLq (2 * ε * c) 2 G ^ (2 : ℝ) =
      (ENNReal.ofReal ε * IIIa.ltauLq (2 * ε * c) 2 G) ^ (2 : ℝ) := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2),
      ENNReal.ofReal_rpow_of_nonneg hε.le (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_two]
  calc (∫⁻ p, ENNReal.ofReal p.1⁻¹ * G (NearInst.chartTau ε⁻¹ p) (NearInst.chartY ε⁻¹ p) ^ (2 : ℝ)
        ∂srcMeasure c) ^ (1 / 2 : ℝ)
      ≤ (ENNReal.ofReal (ε ^ 2) * IIIa.ltauLq (2 * ε * c) 2 G ^ (2 : ℝ)) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow hL (by norm_num)
    _ = ENNReal.ofReal ε * IIIa.ltauLq (2 * ε * c) 2 G := by
        rw [hsq, ← ENNReal.rpow_mul]
        norm_num

/-! ## 4. Real bookkeeping -/

theorem tmc_sqrt_gap (ν R : ℝ) : transGap ν R = (1 - Real.sqrt (5 / 6)) * (R * Real.sqrt ν) := by
  unfold transGap
  have hsq : Real.sqrt (5 * ν / 6) = Real.sqrt (5 / 6) * Real.sqrt ν := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 5 / 6)]
    congr 1
    ring
  rw [hsq]
  ring

theorem tmc_transLen (ν R : ℝ) : transLen ν R = R * Real.sqrt ν := rfl

theorem tmc_rpow_L (ε ν : ℝ) (hε : 0 < ε) (hν : 0 < ν) (e : ℝ) :
    (ε⁻¹ * Real.sqrt ν) ^ e = ε ^ (-e) * ν ^ (e / 2) := by
  rw [Real.mul_rpow (inv_nonneg.2 hε.le) (Real.sqrt_nonneg _), Real.inv_rpow hε.le,
    Real.rpow_neg hε.le, Real.sqrt_eq_rpow, ← Real.rpow_mul hν.le]
  rw [show e / 2 = 1 / 2 * e by ring]

theorem tmc_rpow_nu (ν : ℝ) (hν : 0 < ν) (hν1 : ν ≤ 1) (y : ℝ) (hy : -3 ≤ y) :
    ν ^ y ≤ ν⁻¹ ^ (3 : ℕ) := by
  calc ν ^ y ≤ ν ^ (-3 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hν hν1 hy
    _ = ν⁻¹ ^ (3 : ℕ) := by
      rw [show (-3 : ℝ) = -((3 : ℕ) : ℝ) by norm_num, Real.rpow_neg hν.le, Real.rpow_natCast,
        inv_pow]

theorem tmc_rpow_inv_sq (L : ℝ) (hL : 0 < L) : L⁻¹ ^ (2 : ℕ) = L ^ (-(2 : ℝ)) := by
  rw [Real.rpow_neg hL.le, Real.rpow_two, inv_pow]

theorem tmc_RW (ε ν CY : ℝ) (ha : 0 < 1 - Real.sqrt (5 / 6)) (hε : 0 < ε) (hν : 0 < ν)
    (hν1 : ν ≤ 1) (hCY : 0 ≤ CY) :
    ε * (CY * transGap ν ε⁻¹ ^ (-(23 / 11 : ℝ))) ≤
      CY * (1 - Real.sqrt (5 / 6)) ^ (-(23 / 11 : ℝ)) * ε ^ (34 / 11 : ℝ) * ν⁻¹ ^ (3 : ℕ) := by
  have hL : 0 < ε⁻¹ * Real.sqrt ν := mul_pos (inv_pos.2 hε) (Real.sqrt_pos.2 hν)
  rw [tmc_sqrt_gap, Real.mul_rpow ha.le hL.le, tmc_rpow_L ε ν hε hν]
  have e3 : ε ^ (34 / 11 : ℝ) = ε * ε ^ (-(-(23 / 11 : ℝ))) := by
    rw [show (34 / 11 : ℝ) = 1 + -(-(23 / 11 : ℝ)) by norm_num, Real.rpow_add hε, Real.rpow_one]
  have hnu := tmc_rpow_nu ν hν hν1 (-(23 / 11 : ℝ) / 2) (by norm_num)
  have hpos : 0 ≤ CY * (1 - Real.sqrt (5 / 6)) ^ (-(23 / 11 : ℝ)) * ε ^ (34 / 11 : ℝ) :=
    mul_nonneg (mul_nonneg hCY (Real.rpow_nonneg ha.le _)) (Real.rpow_nonneg hε.le _)
  calc ε * (CY * ((1 - Real.sqrt (5 / 6)) ^ (-(23 / 11 : ℝ)) *
          (ε ^ (-(-(23 / 11 : ℝ))) * ν ^ (-(23 / 11 : ℝ) / 2))))
      = (CY * (1 - Real.sqrt (5 / 6)) ^ (-(23 / 11 : ℝ)) * ε ^ (34 / 11 : ℝ)) *
          ν ^ (-(23 / 11 : ℝ) / 2) := by
        rw [e3]; ring
    _ ≤ (CY * (1 - Real.sqrt (5 / 6)) ^ (-(23 / 11 : ℝ)) * ε ^ (34 / 11 : ℝ)) *
          ν⁻¹ ^ (3 : ℕ) := mul_le_mul_of_nonneg_left hnu hpos
    _ = CY * (1 - Real.sqrt (5 / 6)) ^ (-(23 / 11 : ℝ)) * ε ^ (34 / 11 : ℝ) * ν⁻¹ ^ (3 : ℕ) :=
        rfl

theorem tmc_RD (ε ν CY1 : ℝ) (ha : 0 < 1 - Real.sqrt (5 / 6)) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hν : 0 < ν) (hν1 : ν ≤ 1) (hCY : 0 ≤ CY1) :
    ε * ((transLen ν ε⁻¹)⁻¹ * (CY1 * transGap ν ε⁻¹ ^ (-(34 / 11 : ℝ)))) ≤
      CY1 * (1 - Real.sqrt (5 / 6)) ^ (-(34 / 11 : ℝ)) * ε ^ (34 / 11 : ℝ) * ν⁻¹ ^ (3 : ℕ) := by
  have hL : 0 < ε⁻¹ * Real.sqrt ν := mul_pos (inv_pos.2 hε) (Real.sqrt_pos.2 hν)
  rw [tmc_transLen, tmc_sqrt_gap, Real.mul_rpow ha.le hL.le,
    show (ε⁻¹ * Real.sqrt ν)⁻¹ = (ε⁻¹ * Real.sqrt ν) ^ (-1 : ℝ) from (Real.rpow_neg_one _).symm]
  have e4 : ε ^ (56 / 11 : ℝ) = ε * ε ^ (-(-1 + -(34 / 11 : ℝ))) := by
    rw [show (56 / 11 : ℝ) = 1 + -(-1 + -(34 / 11 : ℝ)) by norm_num, Real.rpow_add hε,
      Real.rpow_one]
  have hεle : ε ^ (56 / 11 : ℝ) ≤ ε ^ (34 / 11 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hε hε1 (by norm_num)
  have hnu := tmc_rpow_nu ν hν hν1 ((-1 + -(34 / 11 : ℝ)) / 2) (by norm_num)
  have hK : 0 ≤ CY1 * (1 - Real.sqrt (5 / 6)) ^ (-(34 / 11 : ℝ)) :=
    mul_nonneg hCY (Real.rpow_nonneg ha.le _)
  calc ε * ((ε⁻¹ * Real.sqrt ν) ^ (-1 : ℝ) * (CY1 * ((1 - Real.sqrt (5 / 6)) ^ (-(34 / 11 : ℝ)) *
          (ε⁻¹ * Real.sqrt ν) ^ (-(34 / 11 : ℝ)))))
      = CY1 * (1 - Real.sqrt (5 / 6)) ^ (-(34 / 11 : ℝ)) * ε *
          ((ε⁻¹ * Real.sqrt ν) ^ (-1 : ℝ) * (ε⁻¹ * Real.sqrt ν) ^ (-(34 / 11 : ℝ))) := by ring
    _ = CY1 * (1 - Real.sqrt (5 / 6)) ^ (-(34 / 11 : ℝ)) * ε *
          (ε⁻¹ * Real.sqrt ν) ^ (-1 + -(34 / 11 : ℝ)) := by
        rw [← Real.rpow_add hL]
    _ = CY1 * (1 - Real.sqrt (5 / 6)) ^ (-(34 / 11 : ℝ)) * ε *
          (ε ^ (-(-1 + -(34 / 11 : ℝ))) * ν ^ ((-1 + -(34 / 11 : ℝ)) / 2)) := by
        rw [tmc_rpow_L ε ν hε hν]
    _ = (CY1 * (1 - Real.sqrt (5 / 6)) ^ (-(34 / 11 : ℝ)) * ε ^ (56 / 11 : ℝ)) *
          ν ^ ((-1 + -(34 / 11 : ℝ)) / 2) := by
        rw [e4]; ring
    _ ≤ (CY1 * (1 - Real.sqrt (5 / 6)) ^ (-(34 / 11 : ℝ)) * ε ^ (34 / 11 : ℝ)) *
          ν⁻¹ ^ (3 : ℕ) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hεle hK) hnu (Real.rpow_nonneg hν.le _)
          (mul_nonneg hK (Real.rpow_nonneg hε.le _))
    _ = CY1 * (1 - Real.sqrt (5 / 6)) ^ (-(34 / 11 : ℝ)) * ε ^ (34 / 11 : ℝ) *
          ν⁻¹ ^ (3 : ℕ) := rfl

theorem tmc_RS (ε ν CO : ℝ) (hε : 0 < ε) (hν : 0 < ν) (hν1 : ν ≤ 1) (hCO : 0 ≤ CO) :
    ε * ((transLen ν ε⁻¹)⁻¹ ^ (2 : ℕ) * (CO * transLen ν ε⁻¹ ^ (-(1 / 11 : ℝ)))) ≤
      CO * ε ^ (34 / 11 : ℝ) * ν⁻¹ ^ (3 : ℕ) := by
  have hL : 0 < ε⁻¹ * Real.sqrt ν := mul_pos (inv_pos.2 hε) (Real.sqrt_pos.2 hν)
  rw [tmc_transLen, tmc_rpow_inv_sq _ hL]
  have e1 : (ε⁻¹ * Real.sqrt ν) ^ (-(2 : ℝ)) * (ε⁻¹ * Real.sqrt ν) ^ (-(1 / 11 : ℝ)) =
      (ε⁻¹ * Real.sqrt ν) ^ (-(23 / 11 : ℝ)) := by
    rw [← Real.rpow_add hL]
    norm_num
  have e2 : (ε⁻¹ * Real.sqrt ν) ^ (-(23 / 11 : ℝ)) =
      ε ^ (23 / 11 : ℝ) * ν ^ (-(23 / 22 : ℝ)) := by
    rw [tmc_rpow_L ε ν hε hν]
    norm_num
  have e3 : ε ^ (34 / 11 : ℝ) = ε * ε ^ (23 / 11 : ℝ) := by
    rw [show (34 / 11 : ℝ) = 1 + 23 / 11 by norm_num, Real.rpow_add hε, Real.rpow_one]
  have hnu := tmc_rpow_nu ν hν hν1 (-(23 / 22 : ℝ)) (by norm_num)
  calc ε * ((ε⁻¹ * Real.sqrt ν) ^ (-(2 : ℝ)) * (CO * (ε⁻¹ * Real.sqrt ν) ^ (-(1 / 11 : ℝ))))
      = CO * ((ε⁻¹ * Real.sqrt ν) ^ (-(2 : ℝ)) * (ε⁻¹ * Real.sqrt ν) ^ (-(1 / 11 : ℝ))) * ε := by
        ring
    _ = CO * (ε ^ (23 / 11 : ℝ) * ν ^ (-(23 / 22 : ℝ))) * ε := by rw [e1, e2]
    _ = CO * ε ^ (34 / 11 : ℝ) * ν ^ (-(23 / 22 : ℝ)) := by rw [e3]; ring
    _ ≤ CO * ε ^ (34 / 11 : ℝ) * ν⁻¹ ^ (3 : ℕ) :=
        mul_le_mul_of_nonneg_left hnu (mul_nonneg hCO (Real.rpow_nonneg hε.le _))
    _ = CO * ε ^ (34 / 11 : ℝ) * ν⁻¹ ^ (3 : ℕ) := rfl

theorem tmc_comb (ε KW KD KS M : ℝ) (X : ℝ≥0∞) (hε : 0 ≤ ε) (h1 : 0 ≤ KW) (h2 : 0 ≤ KD)
    (h3 : 0 ≤ KS) (hM : ε * KW + ε * KD + ε * KS ≤ M) :
    ENNReal.ofReal ε * (ENNReal.ofReal KW * X) + ENNReal.ofReal ε * (ENNReal.ofReal KD * X) +
      ENNReal.ofReal ε * (ENNReal.ofReal KS * X) ≤ ENNReal.ofReal M * X := by
  have hA : ENNReal.ofReal (ε * KW + ε * KD + ε * KS) = ENNReal.ofReal (ε * KW + ε * KD) +
      ENNReal.ofReal (ε * KS) := by
    rw [ENNReal.ofReal_add (add_nonneg (mul_nonneg hε h1) (mul_nonneg hε h2))
      (mul_nonneg hε h3)]
  have hB : ENNReal.ofReal (ε * KW + ε * KD) = ENNReal.ofReal (ε * KW) + ENNReal.ofReal (ε * KD) := by
    rw [ENNReal.ofReal_add (mul_nonneg hε h1) (mul_nonneg hε h2)]
  have heq : ENNReal.ofReal ε * (ENNReal.ofReal KW * X) + ENNReal.ofReal ε * (ENNReal.ofReal KD * X) +
      ENNReal.ofReal ε * (ENNReal.ofReal KS * X) =
      ENNReal.ofReal (ε * KW + ε * KD + ε * KS) * X := by
    rw [hA, hB, ENNReal.ofReal_mul hε, ENNReal.ofReal_mul hε, ENNReal.ofReal_mul hε]
    ring
  rw [heq]
  exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hM) zero_le

/-! ## 5. The chart bound -/

/-- **`TransMajChart`** (source 2683-2689, 3651-3656, 5590-5592). -/
theorem transMajChart : TransMajChart := by
  have hs1 : Real.sqrt (5 / 6 : ℝ) < 1 := by
    have h := Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 5 / 6) (by norm_num : (5 / 6 : ℝ) < 1)
    rwa [Real.sqrt_one] at h
  have ha : 0 < 1 - Real.sqrt (5 / 6 : ℝ) := by linarith
  obtain ⟨CY, hCY0, hY0⟩ := sepDomYoung 0 (22 / 19) 2 (11 / 7) (13 / 22)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨CY1, hCY10, hY1⟩ := sepDomYoung 1 (22 / 19) 2 (11 / 7) (13 / 22)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hOM : OutMajAnnulusL2 := outMajAnnulusL2
  obtain ⟨CO, hCO0, hO⟩ := hOM
  unfold TransMajChart
  refine ⟨CY * (1 - Real.sqrt (5 / 6)) ^ (-(23 / 11 : ℝ)) +
    CY1 * (1 - Real.sqrt (5 / 6)) ^ (-(34 / 11 : ℝ)) + CO, 3, ?_, ?_⟩
  · have h1 : 0 ≤ CY * (1 - Real.sqrt (5 / 6)) ^ (-(23 / 11 : ℝ)) :=
      mul_nonneg hCY0 (Real.rpow_nonneg ha.le _)
    have h2 : 0 ≤ CY1 * (1 - Real.sqrt (5 / 6)) ^ (-(34 / 11 : ℝ)) :=
      mul_nonneg hCY10 (Real.rpow_nonneg ha.le _)
    linarith
  intro ν ε c hν hν1 hε hε1 hc T hT hA
  have hR : (0 : ℝ) < ε⁻¹ := inv_pos.2 hε
  have hP : 0 < 2 * ε * c := mul_pos (mul_pos two_pos hε) hc
  have hLnn0 : 0 ≤ transLen ν ε⁻¹ := by
    rw [tmc_transLen]; exact mul_nonneg (inv_nonneg.2 hε.le) (Real.sqrt_nonneg _)
  have hDpos : 0 < transGap ν ε⁻¹ := by
    rw [tmc_sqrt_gap]; exact mul_pos ha (mul_pos hR (Real.sqrt_pos.2 hν))
  have hgm : Measurable (Function.uncurry (IIIa.srcNorm T)) := srcNorm_measurable hT
  have hgp : ∀ τ z, IIIa.srcNorm T (τ + 2 * ε * c) z = IIIa.srcNorm T τ z := by
    intro τ z
    unfold IIIa.srcNorm
    rw [hT.periodic]
  have hgs : ∀ τ z, ε⁻¹ * Real.sqrt (5 * ν / 6) < ϱ z → IIIa.srcNorm T τ z = 0 := by
    intro τ z hz
    have h0 : T τ z = 0 := hT.support τ z hz
    unfold IIIa.srcNorm
    rw [h0]
    simp [IIIa.tensorNorm]
  obtain ⟨cgW, cgD, cgS⟩ := transMajFacts ν ε⁻¹ (2 * ε * c) hν hR hP T hT hA
  -- W part
  have hWb : IIIa.ltauLq (2 * ε * c) 2 (transMajW ν ε⁻¹ (IIIa.srcNorm T)) ≤
      ENNReal.ofReal (CY * transGap ν ε⁻¹ ^ (-(23 / 11 : ℝ))) *
        IIIa.ltauLq (2 * ε * c) (22 / 19) (IIIa.srcNorm T) := by
    have hpt : ∀ τ y, transMajW ν ε⁻¹ (IIIa.srcNorm T) τ y ≤
        IIIa.sepDom 0 0 (transGap ν ε⁻¹) (IIIa.srcNorm T) τ y :=
      fun τ y => Set.indicator_le_self' (fun _ _ => zero_le) y
    have h2 := hY0 0 le_rfl (by norm_num) (transGap ν ε⁻¹) (2 * ε * c) hDpos hP
      (IIIa.srcNorm T) hgm hgp
    rw [show (-4 - ((0 : ℕ) : ℝ) + 3 / (11 / 7 : ℝ)) = -(23 / 11 : ℝ) by norm_num] at h2
    exact (IIIa.ltauLq_mono (2 * ε * c) 2 (by norm_num) hpt).trans h2
  -- D part
  have hDb : IIIa.ltauLq (2 * ε * c) 2 (transMajD ν ε⁻¹ (IIIa.srcNorm T)) ≤
      ENNReal.ofReal ((transLen ν ε⁻¹)⁻¹ * (CY1 * transGap ν ε⁻¹ ^ (-(34 / 11 : ℝ)))) *
        IIIa.ltauLq (2 * ε * c) (22 / 19) (IIIa.srcNorm T) := by
    have hpt : ∀ τ y, transMajD ν ε⁻¹ (IIIa.srcNorm T) τ y ≤
        ENNReal.ofReal (transLen ν ε⁻¹)⁻¹ * IIIa.sepDom 0 1 (transGap ν ε⁻¹) (IIIa.srcNorm T) τ y :=
      fun τ y => Set.indicator_le_self' (fun _ _ => zero_le) y
    have hm1 := (IIIa.ltauLq_mono (2 * ε * c) 2 (by norm_num) hpt).trans_eq
      (IIIa.ltauLq_const_mul (2 * ε * c) 2 (by norm_num) _ ENNReal.ofReal_ne_top _)
    have h2 := hY1 0 le_rfl (by norm_num) (transGap ν ε⁻¹) (2 * ε * c) hDpos hP
      (IIIa.srcNorm T) hgm hgp
    rw [show (-4 - ((1 : ℕ) : ℝ) + 3 / (11 / 7 : ℝ)) = -(34 / 11 : ℝ) by norm_num] at h2
    refine hm1.trans (le_trans (mul_le_mul_of_nonneg_left h2 zero_le) (le_of_eq ?_))
    rw [ENNReal.ofReal_mul (inv_nonneg.2 hLnn0)]
    ring
  -- S part
  have hSb : IIIa.ltauLq (2 * ε * c) 2 (transMajS ν ε⁻¹ (IIIa.srcNorm T)) ≤
      ENNReal.ofReal ((transLen ν ε⁻¹)⁻¹ ^ 2 * (CO * transLen ν ε⁻¹ ^ (-(1 / 11 : ℝ)))) *
        IIIa.ltauLq (2 * ε * c) (22 / 19) (IIIa.srcNorm T) := by
    have hfun : transMajS ν ε⁻¹ (IIIa.srcNorm T) = fun τ y =>
        ENNReal.ofReal ((transLen ν ε⁻¹)⁻¹ ^ 2) * (streamAnn ν ε⁻¹).indicator
          (fun y => outMaj 0 (transGap ν ε⁻¹) (IIIa.srcNorm T) τ (ϱ y) (y 2)) y := by
      funext τ y
      unfold transMajS
      by_cases hy : y ∈ streamAnn ν ε⁻¹ <;> simp [Set.indicator, hy]
    have hO' := hO ν ε⁻¹ (2 * ε * c) 0 hν hR hP le_rfl (IIIa.srcNorm T) hgm hgp hgs
    rw [hfun, IIIa.ltauLq_const_mul (2 * ε * c) 2 (by norm_num) _ ENNReal.ofReal_ne_top _]
    rw [tmc_transLen]
    refine le_trans (mul_le_mul_of_nonneg_left hO' zero_le) (le_of_eq ?_)
    rw [ENNReal.ofReal_mul (sq_nonneg _)]
    ring
  -- chart comparison for the three components
  have hA1 := tmc_chart_comp ε c hε hc (transMajW ν ε⁻¹ (IIIa.srcNorm T)) cgW
  have hA2 := tmc_chart_comp ε c hε hc (transMajD ν ε⁻¹ (IIIa.srcNorm T)) cgD
  have hA3 := tmc_chart_comp ε c hε hc (transMajS ν ε⁻¹ (IIIa.srcNorm T)) cgS
  have hmW := tmc_meas_comp cgW.1 ε⁻¹
  have hmD := tmc_meas_comp cgD.1 ε⁻¹
  have hmS := tmc_meas_comp cgS.1 ε⁻¹
  refine le_trans (tmc_mink c _ _ _ hmW hmD hmS) ?_
  refine le_trans (add_le_add (add_le_add (hA1.trans (mul_le_mul_of_nonneg_left hWb zero_le))
    (hA2.trans (mul_le_mul_of_nonneg_left hDb zero_le))) (hA3.trans (mul_le_mul_of_nonneg_left hSb zero_le))) ?_
  -- real bookkeeping
  have hKW : 0 ≤ CY * transGap ν ε⁻¹ ^ (-(23 / 11 : ℝ)) :=
    mul_nonneg hCY0 (Real.rpow_nonneg hDpos.le _)
  have hKD : 0 ≤ (transLen ν ε⁻¹)⁻¹ * (CY1 * transGap ν ε⁻¹ ^ (-(34 / 11 : ℝ))) :=
    mul_nonneg (inv_nonneg.2 hLnn0) (mul_nonneg hCY10 (Real.rpow_nonneg hDpos.le _))
  have hKS : 0 ≤ (transLen ν ε⁻¹)⁻¹ ^ 2 * (CO * transLen ν ε⁻¹ ^ (-(1 / 11 : ℝ))) :=
    mul_nonneg (sq_nonneg _) (mul_nonneg hCO0 (Real.rpow_nonneg hLnn0 _))
  have r1 := tmc_RW ε ν CY ha hε hν hν1 hCY0
  have r2 := tmc_RD ε ν CY1 ha hε hε1 hν hν1 hCY10
  have r3 := tmc_RS ε ν CO hε hν hν1 hCO0
  have hM : ε * (CY * transGap ν ε⁻¹ ^ (-(23 / 11 : ℝ))) +
      ε * ((transLen ν ε⁻¹)⁻¹ * (CY1 * transGap ν ε⁻¹ ^ (-(34 / 11 : ℝ)))) +
      ε * ((transLen ν ε⁻¹)⁻¹ ^ 2 * (CO * transLen ν ε⁻¹ ^ (-(1 / 11 : ℝ)))) ≤
      (CY * (1 - Real.sqrt (5 / 6)) ^ (-(23 / 11 : ℝ)) +
        CY1 * (1 - Real.sqrt (5 / 6)) ^ (-(34 / 11 : ℝ)) + CO) * ν⁻¹ ^ (3 : ℕ) *
        ε ^ (34 / 11 : ℝ) := by
    have hsum := add_le_add (add_le_add r1 r2) r3
    calc _ ≤ _ := hsum
      _ = _ := by ring
  exact tmc_comb ε _ _ _ _ _ hε.le hKW hKD hKS hM

end UnforcedLeray.Short.PartIIIb.Concrete
