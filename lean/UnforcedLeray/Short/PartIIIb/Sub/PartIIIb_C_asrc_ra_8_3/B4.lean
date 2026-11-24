import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_8_3_1

/-!
# `ComparisonExpConv` (`PartIII-b:C/asrc/ra/8/3/1/4`)

Source: `the November 2 reference manuscript` 291-303, 4371.

For `0 < s ≤ 1.1/ν` and `ν ≤ 1/2`: `a = width ν s = 1 + νs ∈ [1, 2.1]`, `c = cOf ν = ν⁻²`,
`c² ≥ 16 ≥ a`.  Then `a^e ≤ 1` for `e ≤ 0`, `e^{-b c²/a} ≤ e^{-bσ c²}` with `bσ = min(b0,b1)/3`
(since `b ≥ 3 bσ` and `a ≤ 2.1`), and `deltaBase 0 bσ ν = e^{-bσ c²}`.  Take `Csig = 0`,
`k = 1`, `C = max C0 C1`, `ν₀ = 1/2`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem comparisonExpConv_proof : ComparisonExpConv := by
  unfold ComparisonExpConv
  intro C0 b0 C1 b1 hC0 hb0 hC1 hb1
  have hbs : 0 < min b0 b1 / 3 := div_pos (lt_min hb0 hb1) (by norm_num)
  refine ⟨0, min b0 b1 / 3, max C0 C1, 1, 1 / 2, hbs, by norm_num, ?_⟩
  intro ν hν hνle s hs hs'
  rw [trainPeriod_two_eq hν]
  have hνs : s * ν ≤ 11 / 10 := (le_div_iff₀ hν).1 hs'
  have hνs' : ν * s ≤ 11 / 10 := by linarith [mul_comm ν s]
  have hνs0 : 0 < ν * s := mul_pos hν hs
  have hν2 : ν ^ 2 ≤ 1 / 4 := by nlinarith
  have hcO : cOf ν * ν ^ 2 = 1 := by
    unfold cOf
    exact inv_mul_cancel₀ (pow_ne_zero 2 hν.ne')
  have hcOpos : 0 < cOf ν := by
    unfold cOf
    positivity
  have hc4 : 4 ≤ cOf ν := by
    nlinarith [mul_le_mul_of_nonneg_left hν2 hcOpos.le]
  have hQ : 16 ≤ cOf ν ^ 2 := by nlinarith
  set a := UnforcedLeray.Train.width ν s with ha_def
  have ha1 : 1 ≤ a := by
    rw [ha_def]
    unfold UnforcedLeray.Train.width
    linarith
  have ha2 : a ≤ 21 / 10 := by
    rw [ha_def]
    unfold UnforcedLeray.Train.width
    linarith
  have ha0 : 0 < a := by linarith
  have hwQ : a ≤ cOf ν ^ 2 := by linarith
  have key : ∀ (Cj bj e : ℝ), 0 < Cj → Cj ≤ max C0 C1 → 3 * (min b0 b1 / 3) ≤ bj → e ≤ 0 →
      Cj * ν⁻¹ * a ^ e * Real.exp (-(bj * cOf ν ^ 2 / a)) ≤
        max C0 C1 * ν⁻¹ ^ 1 * deltaBase 0 (min b0 b1 / 3) ν := by
    intro Cj bj e hCj hCjle hbj he
    have hr : a ^ e ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos ha1 he
    have hr0 : 0 ≤ a ^ e := Real.rpow_nonneg ha0.le e
    have hQ0 : 0 ≤ cOf ν ^ 2 := sq_nonneg _
    have hbsQ : min b0 b1 / 3 * cOf ν ^ 2 ≤ bj * cOf ν ^ 2 / a := by
      rw [le_div_iff₀ ha0]
      have h1 : 0 ≤ min b0 b1 / 3 * cOf ν ^ 2 :=
        mul_nonneg (div_nonneg (le_min hb0.le hb1.le) (by norm_num)) hQ0
      nlinarith [mul_le_mul_of_nonneg_left ha2 h1, mul_le_mul_of_nonneg_right hbj hQ0]
    have hex : Real.exp (-(bj * cOf ν ^ 2 / a)) ≤ Real.exp (-(min b0 b1 / 3 * cOf ν ^ 2)) :=
      Real.exp_le_exp.2 (by linarith)
    have hp : 0 ≤ Cj * ν⁻¹ := mul_nonneg hCj.le (inv_nonneg.2 hν.le)
    have hdel : deltaBase 0 (min b0 b1 / 3) ν = Real.exp (-(min b0 b1 / 3 * cOf ν ^ 2)) := by
      unfold deltaBase
      congr 1
      rw [zero_div, zero_sub]
    rw [hdel, pow_one]
    have hCjM : Cj * ν⁻¹ ≤ max C0 C1 * ν⁻¹ :=
      mul_le_mul_of_nonneg_right hCjle (inv_nonneg.2 hν.le)
    calc Cj * ν⁻¹ * a ^ e * Real.exp (-(bj * cOf ν ^ 2 / a))
        ≤ Cj * ν⁻¹ * 1 * Real.exp (-(bj * cOf ν ^ 2 / a)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr hp) (Real.exp_nonneg _)
      _ = Cj * ν⁻¹ * Real.exp (-(bj * cOf ν ^ 2 / a)) := by rw [mul_one]
      _ ≤ Cj * ν⁻¹ * Real.exp (-(min b0 b1 / 3 * cOf ν ^ 2)) :=
          mul_le_mul_of_nonneg_left hex hp
      _ ≤ max C0 C1 * ν⁻¹ * Real.exp (-(min b0 b1 / 3 * cOf ν ^ 2)) :=
          mul_le_mul_of_nonneg_right hCjM (Real.exp_nonneg _)
  refine ⟨hwQ, ?_, ?_⟩
  · exact key C0 b0 _ hC0 (le_max_left _ _)
      (by have := min_le_left b0 b1; linarith) (by norm_num)
  · exact key C1 b1 _ hC1 (le_max_right _ _)
      (by have := min_le_right b0 b1; linarith) (by norm_num)

end UnforcedLeray.Short.PartIIIb.Concrete
