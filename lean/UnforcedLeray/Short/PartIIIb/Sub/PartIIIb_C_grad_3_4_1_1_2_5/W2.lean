import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_1_2.Vj

/-!
# `PartIII-b:C/grad/3/4/1/1/2/5/1`: weight-two x-derivative bounds of `V_j`

Source `the November 2 reference manuscript`
4963-4980, 5036-5039, 5063-5079.

This is `gradVjBounds` (Vj.lean) with the weight `(1 + |u| + |η|)` raised to the power two.
Every term is absorbed into `latticeW gradAlpha gradK` using `gv2_main`: a factor
`B² · P · T` with `P ≤ 4B⁴` and `T ≤ e^{-(u²+η²)/9}` is at most `4 · B¹² e^{-(u²+η²)/9}`.
-/

set_option autoImplicit false

noncomputable section

open Real

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Weight-two absorption: `B² (T P) ≤ 4 · latticeW` for `T ≤ e^{-(u²+η²)/9}`, `P ≤ 4B⁴`. -/
lemma gv2_main (u η T P : ℝ) (hT : 0 ≤ T) (hTle : T ≤ Real.exp (-(1 / 9) * (u ^ 2 + η ^ 2)))
    (hP : P ≤ 4 * (1 + |u| + |η|) ^ 4) :
    (1 + |u| + |η|) ^ 2 * (T * P) ≤ 4 * latticeW gradAlpha gradK u η := by
  have hB1 : (1 : ℝ) ≤ 1 + |u| + |η| := by linarith [abs_nonneg u, abs_nonneg η]
  rw [gv_L_eq]
  calc (1 + |u| + |η|) ^ 2 * (T * P) = ((1 + |u| + |η|) ^ 2 * P) * T := by ring
    _ ≤ ((1 + |u| + |η|) ^ 2 * (4 * (1 + |u| + |η|) ^ 4)) * T :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hP (by positivity)) hT
    _ = 4 * (1 + |u| + |η|) ^ 6 * T := by ring
    _ ≤ 4 * (1 + |u| + |η|) ^ 6 * Real.exp (-(1 / 9) * (u ^ 2 + η ^ 2)) :=
        mul_le_mul_of_nonneg_left hTle (by positivity)
    _ ≤ 4 * (1 + |u| + |η|) ^ 12 * Real.exp (-(1 / 9) * (u ^ 2 + η ^ 2)) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hB1 (by norm_num : (6:ℕ) ≤ 12)) (by norm_num))
          (Real.exp_pos _).le
    _ = 4 * ((1 + |u| + |η|) ^ 12 * Real.exp (-(1 / 9) * (u ^ 2 + η ^ 2))) := by ring

theorem gradVjWeight2 : ∃ C : ℝ, 0 ≤ C ∧ ∀ (ν s : ℝ) (j : ℤ) (x : ℝ × ℝ), 0 < ν → ν ≤ 1 → 0 < s → s ≤ (11 / 10) / ν → ∀ a b : Fin 2, (1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|) ^ 2 * (‖Vj ν s j x‖ + ‖fderiv ℝ (Vj ν s j) x (ei a)‖ + ‖fderiv ℝ (fun y => fderiv ℝ (Vj ν s j) y (ei a)) x (ei b)‖) ≤ C * gradW ν x j := by
  obtain ⟨K2, hK2, hK2b⟩ := hessVjUnif
  refine ⟨4 * (2 + K2), by linarith, ?_⟩
  intro ν s j x hν hν1 hs hs1 a b
  have hνs : ν * s ≤ 11 / 10 := by
    have h := (le_div_iff₀ hν).mp hs1
    linarith [mul_comm s ν]
  have ha1 : 1 ≤ ageA ν s := by unfold ageA; linarith [mul_pos hν hs]
  have ha2 : ageA ν s ≤ 21 / 10 := by unfold ageA; linarith
  have ha0 : 0 < ageA ν s := by linarith
  have hW : gradW ν x j = latticeW gradAlpha gradK (x.1 - (j : ℝ) * cOf ν) x.2 := rfl
  rw [hW]
  have hn0 : 0 ≤ ‖xj ν j x‖ := norm_nonneg _
  have hnx : ‖xj ν j x‖ ≤ 1 + sq2 (xj ν j x) := gv_norm_le _
  have hS0 : 0 ≤ sq2 (xj ν j x) := hu_sq2_nonneg _
  have hT0 : 0 ≤ Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) := (Real.exp_pos _).le
  have hTle : Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s))
      ≤ Real.exp (-(1 / 9) * ((x.1 - (j : ℝ) * cOf ν) ^ 2 + x.2 ^ 2)) :=
    gv_exp_le _ _ hS0 ha1 ha2
  have hE0 : 0 ≤ hsE ν s j x := mul_nonneg (by positivity) hT0
  have hEle : hsE ν s j x ≤ Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) := by
    unfold hsE
    exact mul_le_of_le_one_left hT0 (inv_le_one_of_one_le₀ (by nlinarith [ha1]))
  have hB1 : (1 : ℝ) ≤ 1 + |x.1 - (j : ℝ) * cOf ν| + |x.2| := by
    linarith [abs_nonneg (x.1 - (j : ℝ) * cOf ν), abs_nonneg x.2]
  have hB0 : (0 : ℝ) ≤ 1 + |x.1 - (j : ℝ) * cOf ν| + |x.2| := by linarith
  have hP1 : 1 + sq2 (xj ν j x) ≤ 2 * (1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|) ^ 2 := by
    have h1 := gv_sq_le (x.1 - (j : ℝ) * cOf ν) x.2
    have h2 : (1 : ℝ) ≤ (1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|) ^ 2 := by nlinarith
    have h3 : sq2 (xj ν j x) = (x.1 - (j : ℝ) * cOf ν) ^ 2 + x.2 ^ 2 := rfl
    rw [h3]
    linarith
  have hB4 : (1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|) ^ 2 ≤ (1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|) ^ 4 :=
    pow_le_pow_right₀ hB1 (by norm_num)
  have hP4 : 1 + sq2 (xj ν j x) ≤ 4 * (1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|) ^ 4 := by
    have hB4' : (0 : ℝ) ≤ (1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|) ^ 4 := by positivity
    linarith
  have hP2 : (1 + sq2 (xj ν j x)) ^ 2 ≤ 4 * (1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|) ^ 4 := by
    have h := pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ 1 + sq2 (xj ν j x)) hP1 2
    calc (1 + sq2 (xj ν j x)) ^ 2 ≤ (2 * (1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|) ^ 2) ^ 2 := h
      _ = 4 * (1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|) ^ 4 := by ring
  -- the value `V_j`
  have hV : (1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|) ^ 2 * ‖Vj ν s j x‖
      ≤ 4 * latticeW gradAlpha gradK (x.1 - (j : ℝ) * cOf ν) x.2 := by
    have hVnorm : ‖Vj ν s j x‖ = hsE ν s j x * ‖xj ν j x‖ := by
      have hVeq : Vj ν s j x = hsE ν s j x • Jrot (xj ν j x) := rfl
      rw [hVeq, hs_smul_jrot, abs_of_nonneg hE0]
    have c1 : hsE ν s j x * ‖xj ν j x‖
        ≤ Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) * (1 + sq2 (xj ν j x)) :=
      mul_le_mul hEle hnx hn0 hT0
    calc (1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|) ^ 2 * ‖Vj ν s j x‖
        = (1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|) ^ 2 * (hsE ν s j x * ‖xj ν j x‖) := by
          rw [hVnorm]
      _ ≤ (1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|) ^ 2 *
            (Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) * (1 + sq2 (xj ν j x))) :=
          mul_le_mul_of_nonneg_left c1 (by positivity)
      _ ≤ 4 * latticeW gradAlpha gradK (x.1 - (j : ℝ) * cOf ν) x.2 :=
          gv2_main (x.1 - (j : ℝ) * cOf ν) x.2 _ _ hT0 hTle hP4
  -- the first derivative
  have hG : ‖fderiv ℝ (Vj ν s j) x (ei a)‖ ≤
      Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) * (1 + sq2 (xj ν j x)) := by
    rw [hs_eq]
    have hA : |hsL ν s j a x| ≤ ‖xj ν j x‖ / ageA ν s :=
      (gp_c1_abs (xj ν j x) (ei a) (ageA ν s) ha0).trans
        (div_le_div_of_nonneg_right (mul_le_of_le_one_right hn0 (hs_ei_norm_le a)) ha0.le)
    have hG1 : ‖hsG ν s j a x‖ ≤ hsE ν s j x * 1 + |hsE ν s j x * hsL ν s j a x| * ‖xj ν j x‖ := by
      have hsplit : hsG ν s j a x = hsE ν s j x • Jrot (ei a)
          + (hsE ν s j x * hsL ν s j a x) • Jrot (xj ν j x) := rfl
      rw [hsplit]
      calc _ ≤ ‖hsE ν s j x • Jrot (ei a)‖ + ‖(hsE ν s j x * hsL ν s j a x) • Jrot (xj ν j x)‖ :=
            norm_add_le _ _
        _ = |hsE ν s j x| * ‖ei a‖ + |hsE ν s j x * hsL ν s j a x| * ‖xj ν j x‖ := by
            rw [hs_smul_jrot, hs_smul_jrot]
        _ ≤ hsE ν s j x * 1 + |hsE ν s j x * hsL ν s j a x| * ‖xj ν j x‖ := by
            rw [abs_of_nonneg hE0]
            exact add_le_add (mul_le_mul_of_nonneg_left (hs_ei_norm_le a) hE0) le_rfl
    have hX : |hsE ν s j x * hsL ν s j a x| * ‖xj ν j x‖
        ≤ Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) * sq2 (xj ν j x) := by
      rw [abs_mul, abs_of_nonneg hE0]
      have hX1 : hsE ν s j x * |hsL ν s j a x|
          ≤ Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) * (‖xj ν j x‖ / ageA ν s) :=
        mul_le_mul hEle hA (abs_nonneg _) hT0
      have hX2 : ‖xj ν j x‖ / ageA ν s * ‖xj ν j x‖ ≤ sq2 (xj ν j x) := by
        calc ‖xj ν j x‖ / ageA ν s * ‖xj ν j x‖ ≤ ‖xj ν j x‖ * ‖xj ν j x‖ :=
              mul_le_mul_of_nonneg_right (div_le_self hn0 ha1) hn0
          _ = ‖xj ν j x‖ ^ 2 := by ring
          _ ≤ sq2 (xj ν j x) := hu_norm_sq_le _
      calc hsE ν s j x * |hsL ν s j a x| * ‖xj ν j x‖
          ≤ Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) * (‖xj ν j x‖ / ageA ν s) * ‖xj ν j x‖ :=
            mul_le_mul_of_nonneg_right hX1 hn0
        _ = Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) * (‖xj ν j x‖ / ageA ν s * ‖xj ν j x‖) := by
            ring
        _ ≤ Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) * sq2 (xj ν j x) :=
            mul_le_mul_of_nonneg_left hX2 hT0
    have hE1 : hsE ν s j x * 1 ≤ Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) := by
      rw [mul_one]; exact hEle
    calc ‖hsG ν s j a x‖ ≤ hsE ν s j x * 1 + |hsE ν s j x * hsL ν s j a x| * ‖xj ν j x‖ := hG1
      _ ≤ Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s))
            + Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) * sq2 (xj ν j x) :=
            add_le_add hE1 hX
      _ = Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) * (1 + sq2 (xj ν j x)) := by ring
  have hD1 : (1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|) ^ 2 * ‖fderiv ℝ (Vj ν s j) x (ei a)‖
      ≤ 4 * latticeW gradAlpha gradK (x.1 - (j : ℝ) * cOf ν) x.2 := by
    calc (1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|) ^ 2 * ‖fderiv ℝ (Vj ν s j) x (ei a)‖
        ≤ (1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|) ^ 2 *
            (Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) * (1 + sq2 (xj ν j x))) :=
          mul_le_mul_of_nonneg_left hG (by positivity)
      _ ≤ 4 * latticeW gradAlpha gradK (x.1 - (j : ℝ) * cOf ν) x.2 :=
          gv2_main (x.1 - (j : ℝ) * cOf ν) x.2 _ _ hT0 hTle hP4
  -- the second derivative
  have hD2 := hK2b ν s hν hν1 hs hs1 j x b a
  have hD2' : (1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|) ^ 2
      * ‖fderiv ℝ (fun y => fderiv ℝ (Vj ν s j) y (ei a)) x (ei b)‖
      ≤ K2 * (4 * latticeW gradAlpha gradK (x.1 - (j : ℝ) * cOf ν) x.2) := by
    have hm := gv2_main (x.1 - (j : ℝ) * cOf ν) x.2
      (Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s))) ((1 + sq2 (xj ν j x)) ^ 2)
      hT0 hTle hP2
    calc (1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|) ^ 2
          * ‖fderiv ℝ (fun y => fderiv ℝ (Vj ν s j) y (ei a)) x (ei b)‖
        ≤ (1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|) ^ 2
          * (K2 * ((1 + sq2 (xj ν j x)) ^ 2 * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)))) :=
          mul_le_mul_of_nonneg_left hD2 (by positivity)
      _ = K2 * ((1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|) ^ 2
          * (Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) * (1 + sq2 (xj ν j x)) ^ 2)) := by
          ring
      _ ≤ K2 * (4 * latticeW gradAlpha gradK (x.1 - (j : ℝ) * cOf ν) x.2) :=
          mul_le_mul_of_nonneg_left hm hK2
  calc (1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|) ^ 2 * (‖Vj ν s j x‖ + ‖fderiv ℝ (Vj ν s j) x (ei a)‖
        + ‖fderiv ℝ (fun y => fderiv ℝ (Vj ν s j) y (ei a)) x (ei b)‖)
      = (1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|) ^ 2 * ‖Vj ν s j x‖
        + (1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|) ^ 2 * ‖fderiv ℝ (Vj ν s j) x (ei a)‖
        + (1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|) ^ 2
          * ‖fderiv ℝ (fun y => fderiv ℝ (Vj ν s j) y (ei a)) x (ei b)‖ := by ring
    _ ≤ 4 * latticeW gradAlpha gradK (x.1 - (j : ℝ) * cOf ν) x.2
        + 4 * latticeW gradAlpha gradK (x.1 - (j : ℝ) * cOf ν) x.2
        + K2 * (4 * latticeW gradAlpha gradK (x.1 - (j : ℝ) * cOf ν) x.2) :=
          add_le_add (add_le_add hV hD1) hD2'
    _ = 4 * (2 + K2) * latticeW gradAlpha gradK (x.1 - (j : ℝ) * cOf ν) x.2 := by ring

end UnforcedLeray.Short.PartIIIb.Concrete
