import UnforcedLeray.Short.PartI.Sub.PartI_T02_1_4_4_1_7_1_1_1_1_2_1

/-!
# Part I, `PartI:T02/1/4/4/1/7/1/1/1/1/2/1/2`: the elementary tail inequality `HeatTailElem`

Source `the November 2 reference manuscript`, lines 261-288.
The witness is `C₀ = 200`: for `s ≥ 1`, `0 < h ≤ 1`,
`h⁻¹ · 2 e^{-s²/(4h)} ≤ 200 √h e^{-s²/16}`.
-/

set_option autoImplicit false

noncomputable section

namespace HeatTailElemAux

theorem exp_split {s h : ℝ} (hs : 1 ≤ s) (hh : 0 < h) (hh1 : h ≤ 1) :
    Real.exp (-(s ^ 2) / (4 * h)) ≤ Real.exp (-(3 / (16 * h))) * Real.exp (-(s ^ 2) / 16) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.2
  have hs2 : 1 ≤ s ^ 2 := by nlinarith
  have hsplit : (-(s ^ 2) / (4 * h)) - (-(3 / (16 * h)) + -(s ^ 2) / 16)
      = -((4 * s ^ 2 - 3 - s ^ 2 * h) / (16 * h)) := by
    field_simp
    ring
  have hnum : 0 ≤ 4 * s ^ 2 - 3 - s ^ 2 * h := by
    nlinarith [mul_nonneg (sub_nonneg.2 hs2) (by linarith : (0:ℝ) ≤ 4 - h)]
  have hdiv : 0 ≤ (4 * s ^ 2 - 3 - s ^ 2 * h) / (16 * h) := div_nonneg hnum (by positivity)
  linarith

theorem exp_neg_three_le {h : ℝ} (hh : 0 < h) :
    Real.exp (-(3 / (16 * h))) ≤ 512 * h ^ 2 / 9 := by
  set y : ℝ := 3 / (16 * h) with hy
  have hy0 : 0 ≤ y := by positivity
  have hq : 1 + y + y ^ 2 / 2 ≤ Real.exp y := Real.quadratic_le_exp_of_nonneg hy0
  have hprod : Real.exp (-y) * Real.exp y = 1 := by
    rw [← Real.exp_add]; simp
  have hinv : y ^ 2 / 2 * (512 * h ^ 2 / 9) = 1 := by
    rw [hy]; field_simp; ring
  have hneg : 0 ≤ Real.exp (-y) := (Real.exp_pos _).le
  have hle : y ^ 2 / 2 ≤ Real.exp y := by linarith
  have h1 : Real.exp (-y) * (y ^ 2 / 2) ≤ Real.exp (-y) * Real.exp y :=
    mul_le_mul_of_nonneg_left hle hneg
  have h1' : Real.exp (-y) * (y ^ 2 / 2) ≤ 1 := by linarith [hprod]
  calc Real.exp (-y) = Real.exp (-y) * (y ^ 2 / 2 * (512 * h ^ 2 / 9)) := by rw [hinv, mul_one]
    _ = (Real.exp (-y) * (y ^ 2 / 2)) * (512 * h ^ 2 / 9) := by ring
    _ ≤ 1 * (512 * h ^ 2 / 9) := by
        refine mul_le_mul_of_nonneg_right h1' ?_
        positivity
    _ = 512 * h ^ 2 / 9 := one_mul _

theorem heatTailElem_aux (s h : ℝ) (hs : 1 ≤ s) (hh : 0 < h) (hh1 : h ≤ 1) :
    h⁻¹ * (2 * Real.exp (-(s ^ 2) / (4 * h))) ≤ 200 * Real.sqrt h * Real.exp (-(s ^ 2) / 16) := by
  have hE : 0 ≤ Real.exp (-(s ^ 2) / 16) := (Real.exp_pos _).le
  have hexp := exp_split hs hh hh1
  have hk := exp_neg_three_le hh
  have hsq : Real.sqrt h * Real.sqrt h = h := Real.mul_self_sqrt hh.le
  have hs1 : Real.sqrt h ≤ 1 := by
    calc Real.sqrt h ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hh1
      _ = 1 := Real.sqrt_one
  have hhle : h ≤ Real.sqrt h := by
    nlinarith [mul_nonneg (Real.sqrt_nonneg h) (sub_nonneg.2 hs1)]
  calc h⁻¹ * (2 * Real.exp (-(s ^ 2) / (4 * h)))
      ≤ h⁻¹ * (2 * (Real.exp (-(3 / (16 * h))) * Real.exp (-(s ^ 2) / 16))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp (by norm_num))
          (inv_nonneg.2 hh.le)
    _ = (h⁻¹ * (2 * Real.exp (-(3 / (16 * h))))) * Real.exp (-(s ^ 2) / 16) := by ring
    _ ≤ (h⁻¹ * (2 * (512 * h ^ 2 / 9))) * Real.exp (-(s ^ 2) / 16) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hk (by norm_num))
            (inv_nonneg.2 hh.le)) hE
    _ = (1024 / 9 * h) * Real.exp (-(s ^ 2) / 16) := by
        have hne : h ≠ 0 := hh.ne'
        field_simp
        ring
    _ ≤ 200 * Real.sqrt h * Real.exp (-(s ^ 2) / 16) := by
        refine mul_le_mul_of_nonneg_right ?_ hE
        linarith [hhle, hh]

end HeatTailElemAux

/-- **Leaf E (elementary inequality; source lines 261-288).** -/
theorem heatTailElem : UnforcedLeray.Short.PartI.HeatTailElem := by
  unfold UnforcedLeray.Short.PartI.HeatTailElem
  exact ⟨200, fun s h hs hh hh1 => HeatTailElemAux.heatTailElem_aux s h hs hh hh1⟩
