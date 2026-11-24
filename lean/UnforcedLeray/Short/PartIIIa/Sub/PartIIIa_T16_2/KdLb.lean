import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T16_2
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Integral.MeanInequalities

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

theorem sepKdLb_lintegral_smul_space (c : ℝ) (hc : 0 < c) {f : Space → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x : Space, f (c • x) = ENNReal.ofReal ((c ^ 3)⁻¹) * ∫⁻ x, f x := by
  have h := Measure.map_addHaar_smul (volume : Measure Space) hc.ne'
  have hm : Measurable fun x : Space => c • x := measurable_const_smul c
  rw [← lintegral_map hf hm, h, lintegral_smul_measure]
  simp [finrank_euclideanSpace_fin, abs_of_pos (inv_pos.mpr (pow_pos hc 3))]

theorem sepKdLb_scale (j : ℕ) (D : ℝ) (hD : 0 < D) (x : Space) :
    sepKd j D x = ENNReal.ofReal (D ^ (-(4 + (j : ℝ)))) * sepKd j 1 (D⁻¹ • x) := by
  unfold sepKd
  have hn : ‖D⁻¹ • x‖ = D⁻¹ * ‖x‖ := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hD.le)]
  rw [hn]
  have hiff : D ≤ ‖x‖ ↔ 1 ≤ D⁻¹ * ‖x‖ := by
    rw [← div_eq_inv_mul, le_div_iff₀ hD]; simp
  by_cases h : D ≤ ‖x‖
  · rw [if_pos h, if_pos (hiff.mp h), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have hc : D ^ (-(4 + (j : ℝ))) * (D ^ (-4 - (j : ℝ)))⁻¹ = 1 := by
      rw [show -4 - (j : ℝ) = -(4 + j) by ring]; exact mul_inv_cancel₀ (Real.rpow_pos_of_pos hD _).ne'
    rw [Real.mul_rpow (inv_nonneg.mpr hD.le) (by linarith [norm_nonneg x, hD, h]), Real.inv_rpow hD.le,
      ← mul_assoc, hc, one_mul]
  · rw [if_neg h, if_neg (fun h' => h (hiff.mpr h'))]; simp

theorem sepKdLb_lintegral_one_ne_top (j : ℕ) (b : ℝ) (hb : 1 ≤ b) :
    ∫⁻ x : Space, sepKd j 1 x ^ b ≠ ⊤ := by
  have hs : (Module.finrank ℝ Space : ℝ) < (4 + (j : ℝ)) * b := by
    have h3 : (Module.finrank ℝ Space : ℝ) = 3 := by simp [finrank_euclideanSpace_fin]
    have : (0:ℝ) ≤ j := Nat.cast_nonneg j
    have h4 : (4:ℝ) * b ≤ (4 + j) * b := by nlinarith
    linarith
  have hint := integrable_one_add_norm (E := Space) (μ := volume) hs
  have h2 := hint.lintegral_lt_top
  refine ne_top_of_le_ne_top (b := ENNReal.ofReal (2 ^ ((4 + (j : ℝ)) * b)) *
    ∫⁻ x : Space, ENNReal.ofReal ((1 + ‖x‖) ^ (-((4 + (j : ℝ)) * b)))) ?_ ?_
  · refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top h2.ne
  · rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun x => ?_
    unfold sepKd
    split_ifs with h
    · rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg (norm_nonneg x) _) (by linarith),
        ← Real.rpow_mul (norm_nonneg x), ← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 : 0 < ‖x‖ := by linarith
      have h3 : (1 + ‖x‖) ≤ 2 * ‖x‖ := by linarith
      have h4 : (1 + ‖x‖) ^ (-((4 + (j : ℝ)) * b)) ≥ (2 * ‖x‖) ^ (-((4 + (j : ℝ)) * b)) := by
        apply Real.rpow_le_rpow_of_nonpos (by positivity) h3
        have : (0:ℝ) ≤ j := Nat.cast_nonneg j
        nlinarith
      rw [Real.mul_rpow (by norm_num) h1.le] at h4
      have h5 : (2:ℝ) ^ ((4 + (j : ℝ)) * b) * (2:ℝ) ^ (-((4 + (j : ℝ)) * b)) = 1 := by
        rw [← Real.rpow_add (by norm_num)]; simp
      calc ‖x‖ ^ ((-4 - (j : ℝ)) * b)
          = (2:ℝ) ^ ((4 + (j : ℝ)) * b) * ((2:ℝ) ^ (-((4 + (j : ℝ)) * b)) * ‖x‖ ^ (-((4 + (j : ℝ)) * b))) := by
            rw [← mul_assoc, h5, one_mul]; congr 1; ring
        _ ≤ (2:ℝ) ^ ((4 + (j : ℝ)) * b) * (1 + ‖x‖) ^ (-((4 + (j : ℝ)) * b)) :=
            mul_le_mul_of_nonneg_left h4 (by positivity)
    · rw [ENNReal.zero_rpow_of_pos (by linarith)]; exact bot_le

theorem sepKdLb_lintegral_rpow (j : ℕ) (D b : ℝ) (hD : 0 < D) (hb : 0 < b) :
    ∫⁻ x : Space, sepKd j D x ^ b =
      ENNReal.ofReal (D ^ (3 - (4 + (j : ℝ)) * b)) * ∫⁻ x : Space, sepKd j 1 x ^ b := by
  have hm : Measurable fun x : Space => sepKd j 1 x ^ b := (measurable_sepKd j 1).pow_const b
  have h1 : ∀ x : Space, sepKd j D x ^ b = ENNReal.ofReal (D ^ (-((4 + (j : ℝ)) * b))) *
      (fun x : Space => sepKd j 1 x ^ b) (D⁻¹ • x) := by
    intro x
    rw [sepKdLb_scale j D hD x, ENNReal.mul_rpow_of_nonneg _ _ hb.le,
      ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hD.le _) hb.le, ← Real.rpow_mul hD.le]
    congr 3; ring
  simp_rw [h1]
  have hs := sepKdLb_lintegral_smul_space D⁻¹ (inv_pos.mpr hD) hm
  have hm2 : Measurable fun x : Space => sepKd j 1 (D⁻¹ • x) ^ b := hm.comp (measurable_const_smul D⁻¹)
  rw [lintegral_const_mul _ hm2, hs,
    ← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg hD.le _)]
  congr 2
  rw [inv_pow, inv_inv, ← Real.rpow_natCast, ← Real.rpow_add hD]
  congr 1; push_cast; ring

theorem sepKdLb : UnforcedLeray.Short.IIIa.SepKdLb := by
  intro j b hb
  have hI : (∫⁻ x : Space, sepKd j 1 x ^ b) ^ (1 / b) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by positivity) (sepKdLb_lintegral_one_ne_top j b hb)
  refine ⟨((∫⁻ x : Space, sepKd j 1 x ^ b) ^ (1 / b)).toReal, ENNReal.toReal_nonneg, fun D hD => ?_⟩
  rw [sepKdLb_lintegral_rpow j D b hD (by linarith), ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
    ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hD.le _) (by positivity), ← Real.rpow_mul hD.le]
  have hexp : (3 - (4 + (j : ℝ)) * b) * (1 / b) = -4 - (j : ℝ) + 3 / b := by
    field_simp; ring
  rw [hexp]
  conv_lhs => rw [← ENNReal.ofReal_toReal hI]
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hD.le _)]
  exact le_of_eq (congr_arg _ (mul_comm _ _))

end UnforcedLeray.Short.IIIa
