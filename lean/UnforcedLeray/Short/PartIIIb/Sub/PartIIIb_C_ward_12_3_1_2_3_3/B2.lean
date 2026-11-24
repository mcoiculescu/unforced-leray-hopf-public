import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_3_3
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Data.Real.ConjExponents
import Mathlib.Analysis.Normed.Group.Real

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology

theorem holderStep : HolderStep := by
  intro μ G H C hG hH hGq hineq
  have hqr : UnforcedLeray.B0412.q0E.toReal = 11 / 4 := UnforcedLeray.B0412.q0E_toReal
  have hsr : ((2 : ℝ≥0∞) * UnforcedLeray.B0412.q0E).toReal = 11 / 2 := by
    rw [ENNReal.toReal_mul, hqr]
    norm_num
  have hq0 : UnforcedLeray.B0412.q0E ≠ 0 :=
    (zero_lt_one.trans UnforcedLeray.B0412.one_lt_q0E).ne'
  have hqtop : UnforcedLeray.B0412.q0E ≠ ⊤ := UnforcedLeray.B0412.q0E_ne_top
  have h2ne : (2 : ℝ≥0∞) * UnforcedLeray.B0412.q0E ≠ 0 := mul_ne_zero two_ne_zero hq0
  have h2top : (2 : ℝ≥0∞) * UnforcedLeray.B0412.q0E ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofNat_ne_top hqtop
  have hof : ∀ v : UnforcedLeray.PhaseSpace.CVec3, ENNReal.ofReal ‖v‖ = ‖v‖ₑ := by
    intro v
    rw [← Real.enorm_eq_ofReal (norm_nonneg v)]
    simp
  have convG : ∀ (x : ℝ × UnforcedLeray.Space) (t : ℝ), 0 ≤ t →
      ENNReal.ofReal (‖G x‖ ^ t) = ‖G x‖ₑ ^ t := by
    intro x t ht
    rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) ht, hof]
  -- the L^{2q} side in lintegral form
  have hXtop : (∫⁻ x, ‖G x‖ₑ ^ (11 / 2 : ℝ) ∂μ) ≠ ⊤ := by
    have h := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top h2ne h2top).1 hGq.eLpNorm_lt_top
    rw [hsr] at h
    exact h.ne
  -- rewrite the hypothesis into lintegral form with exponents 11/2, 7/2
  have e1 : ∀ x : ℝ × UnforcedLeray.Space,
      ENNReal.ofReal (‖G x‖ ^ (2 * UnforcedLeray.B0412.q0E.toReal)) = ‖G x‖ₑ ^ (11 / 2 : ℝ) := by
    intro x
    rw [convG x _ (by rw [hqr]; norm_num)]
    congr 1
  have e2 : ∀ x : ℝ × UnforcedLeray.Space,
      ENNReal.ofReal (‖G x‖ ^ (2 * UnforcedLeray.B0412.q0E.toReal - 2) * ‖H x‖) =
        ‖G x‖ₑ ^ (7 / 2 : ℝ) * ‖H x‖ₑ := by
    intro x
    rw [ENNReal.ofReal_mul (Real.rpow_nonneg (norm_nonneg _) _),
      convG x _ (by rw [hqr]; norm_num), hof]
    congr 2
    rw [hqr]
    norm_num
  have hineq' : (∫⁻ x, ‖G x‖ₑ ^ (11 / 2 : ℝ) ∂μ) ≤
      ENNReal.ofReal C * ∫⁻ x, ‖G x‖ₑ ^ (7 / 2 : ℝ) * ‖H x‖ₑ ∂μ := by
    simp only [e1, e2] at hineq
    exact hineq
  -- Hölder with exponents 11/7 and 11/4
  have hH1 : (∫⁻ x, ‖G x‖ₑ ^ (7 / 2 : ℝ) * ‖H x‖ₑ ∂μ) ≤
      (∫⁻ x, ‖G x‖ₑ ^ (11 / 2 : ℝ) ∂μ) ^ (7 / 11 : ℝ) *
        (∫⁻ x, ‖H x‖ₑ ^ (11 / 4 : ℝ) ∂μ) ^ (4 / 11 : ℝ) := by
    have hpq : (11 / 7 : ℝ).HolderConjugate (11 / 4 : ℝ) :=
      Real.holderConjugate_iff.2 ⟨by norm_num, by norm_num⟩
    have hf : AEMeasurable (fun x : ℝ × UnforcedLeray.Space => ‖G x‖ₑ ^ (7 / 2 : ℝ)) μ :=
      (hG.aemeasurable.enorm).pow_const _
    have hg : AEMeasurable (fun x : ℝ × UnforcedLeray.Space => ‖H x‖ₑ) μ :=
      hH.aemeasurable.enorm
    have hm := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq hf hg
    have e3 : ∀ x : ℝ × UnforcedLeray.Space,
        (‖G x‖ₑ ^ (7 / 2 : ℝ)) ^ (11 / 7 : ℝ) = ‖G x‖ₑ ^ (11 / 2 : ℝ) := by
      intro x
      rw [← ENNReal.rpow_mul]
      norm_num
    simp only [e3] at hm
    rw [show (1 : ℝ) / (11 / 7) = 7 / 11 by norm_num,
      show (1 : ℝ) / (11 / 4) = 4 / 11 by norm_num] at hm
    exact hm
  -- rewrite the goal
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal h2ne h2top, hsr,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 hqtop, hqr]
  rw [show (1 : ℝ) / (11 / 2) = 2 / 11 by norm_num,
    show (1 : ℝ) / (11 / 4) = 4 / 11 by norm_num]
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num
  generalize hA : (∫⁻ x, ‖G x‖ₑ ^ (11 / 2 : ℝ) ∂μ) = a at hineq' hH1 hXtop ⊢
  generalize hB : (∫⁻ x, ‖H x‖ₑ ^ (11 / 4 : ℝ) ∂μ) = b at hH1 ⊢
  generalize hZ : (∫⁻ x, ‖G x‖ₑ ^ (7 / 2 : ℝ) * ‖H x‖ₑ ∂μ) = Z at hineq' hH1
  by_cases ha0 : a = 0
  · rw [ha0, ENNReal.zero_rpow_of_pos (by norm_num)]
    simp
  · have hapos : a ^ (7 / 11 : ℝ) ≠ 0 :=
      (ENNReal.rpow_pos (pos_iff_ne_zero.2 ha0) hXtop).ne'
    have hatop : a ^ (7 / 11 : ℝ) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) hXtop
    have hsplit : a = a ^ (7 / 11 : ℝ) * a ^ (4 / 11 : ℝ) := by
      rw [← ENNReal.rpow_add _ _ ha0 hXtop]
      norm_num
    have key : a ^ (7 / 11 : ℝ) * a ^ (4 / 11 : ℝ) ≤
        a ^ (7 / 11 : ℝ) * (ENNReal.ofReal C * b ^ (4 / 11 : ℝ)) := by
      calc a ^ (7 / 11 : ℝ) * a ^ (4 / 11 : ℝ) = a := hsplit.symm
        _ ≤ ENNReal.ofReal C * Z := hineq'
        _ ≤ ENNReal.ofReal C * (a ^ (7 / 11 : ℝ) * b ^ (4 / 11 : ℝ)) := by gcongr
        _ = a ^ (7 / 11 : ℝ) * (ENNReal.ofReal C * b ^ (4 / 11 : ℝ)) := by ring
    exact (ENNReal.mul_le_mul_iff_right hapos hatop).1 key

end UnforcedLeray.Short.PartIIIb.Concrete
