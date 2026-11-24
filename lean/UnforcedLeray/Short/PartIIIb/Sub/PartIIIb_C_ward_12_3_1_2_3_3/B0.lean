import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_3_3
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.Normed.Group.Real

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology

theorem bddMemLpDouble : BddMemLpDouble := by
  intro μ G hG hbd hq
  obtain ⟨K, hK⟩ := hbd
  have hq0 : UnforcedLeray.B0412.q0E ≠ 0 :=
    (zero_lt_one.trans UnforcedLeray.B0412.one_lt_q0E).ne'
  have hqtop : UnforcedLeray.B0412.q0E ≠ ⊤ := UnforcedLeray.B0412.q0E_ne_top
  have h2ne : (2 : ℝ≥0∞) * UnforcedLeray.B0412.q0E ≠ 0 := mul_ne_zero two_ne_zero hq0
  have h2top : (2 : ℝ≥0∞) * UnforcedLeray.B0412.q0E ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofNat_ne_top hqtop
  refine ⟨hG, ?_⟩
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top h2ne h2top]
  have hfin := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hq0 hqtop).1 hq.eLpNorm_lt_top
  have htoReal : ((2 : ℝ≥0∞) * UnforcedLeray.B0412.q0E).toReal = 2 * UnforcedLeray.B0412.q0E.toReal := by
    rw [ENNReal.toReal_mul]
    norm_num
  rw [htoReal]
  set c : ℝ≥0∞ := ENNReal.ofReal K ^ UnforcedLeray.B0412.q0E.toReal with hc_def
  have hc : c ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg ENNReal.ofReal_ne_top
  have key : ∀ x : ℝ × UnforcedLeray.Space,
      ‖G x‖ₑ ^ (2 * UnforcedLeray.B0412.q0E.toReal) ≤ ‖G x‖ₑ ^ UnforcedLeray.B0412.q0E.toReal * c := by
    intro x
    have hx : ‖G x‖ₑ ≤ ENNReal.ofReal K := by
      have h1 : ENNReal.ofReal ‖G x‖ = ‖G x‖ₑ := by
        rw [← Real.enorm_eq_ofReal (norm_nonneg (G x))]
        simp
      rw [← h1]
      exact ENNReal.ofReal_le_ofReal (hK x)
    rw [two_mul, ENNReal.rpow_add_of_nonneg _ _ ENNReal.toReal_nonneg ENNReal.toReal_nonneg]
    exact mul_le_mul_right (ENNReal.rpow_le_rpow hx ENNReal.toReal_nonneg) _
  calc ∫⁻ x, ‖G x‖ₑ ^ (2 * UnforcedLeray.B0412.q0E.toReal) ∂μ
      ≤ ∫⁻ x, ‖G x‖ₑ ^ UnforcedLeray.B0412.q0E.toReal * c ∂μ := lintegral_mono (fun x => key x)
    _ = (∫⁻ x, ‖G x‖ₑ ^ UnforcedLeray.B0412.q0E.toReal ∂μ) * c :=
        lintegral_mul_const' c _ hc
    _ < ⊤ := ENNReal.mul_lt_top hfin hc.lt_top

end UnforcedLeray.Short.PartIIIb.Concrete
