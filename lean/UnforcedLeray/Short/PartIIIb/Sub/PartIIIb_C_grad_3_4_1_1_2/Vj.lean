import UnforcedLeray.Short.PartIIIb.Sub.Leaves.EAcHessUnif
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_1_2.Gauss

/-!
# `PartIII-b:C/grad/3/4/1/1/2/1`: x-derivative bounds of `V_j`

Source `the November 2 reference manuscript`
4963-4980, 5036-5039, 5063-5079.

`V_j = (a²)⁻¹ e^{-|x_j|²/(4a)} J x_j` with `a = 1 + νs ∈ [1, 2.1]`.  The first derivative in a
direction `e_b` is the explicit `hsG` (`hs_eq`), and the second derivatives are bounded by the
uniform leaf `hessVjUnif`.  Every bound is absorbed into `latticeW gradAlpha gradK`, using
`e^{-|x_j|²/(4a)} ≤ e^{-|x_j|²/9}` (since `4a ≤ 9`) and `1 + |x_j|² ≤ 2 (1+|u|+|η|)²`.
-/

set_option autoImplicit false

noncomputable section

open Real

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Unfolding of the weighted Gaussian `latticeW gradAlpha gradK`. -/
lemma gv_L_eq (u η : ℝ) :
    latticeW gradAlpha gradK u η = (1 + |u| + |η|) ^ 12 * Real.exp (-(1 / 9) * (u ^ 2 + η ^ 2)) := by
  unfold latticeW gradAlpha gradK
  rfl

/-- Gaussian rate: `4a ≤ 9` for `a ≤ 21/10`. -/
lemma gv_exp_le (S a : ℝ) (hS : 0 ≤ S) (ha1 : 1 ≤ a) (ha2 : a ≤ 21 / 10) :
    Real.exp (-S / (4 * a)) ≤ Real.exp (-(1 / 9) * S) := by
  apply Real.exp_le_exp.mpr
  have h1 : S / 9 ≤ S / (4 * a) := by
    gcongr <;> linarith
  rw [neg_div]
  linarith

/-- `u² + η² ≤ (1+|u|+|η|)²`. -/
lemma gv_sq_le (u η : ℝ) : u ^ 2 + η ^ 2 ≤ (1 + |u| + |η|) ^ 2 := by
  have hu := abs_nonneg u
  have hη := abs_nonneg η
  nlinarith [sq_abs u, sq_abs η, mul_nonneg hu hη]

/-- `‖y‖ ≤ 1 + |y|²` in the sup norm. -/
lemma gv_norm_le (y : ℝ × ℝ) : ‖y‖ ≤ 1 + sq2 y := by
  have h := hu_norm_sq_le y
  nlinarith [sq_nonneg (‖y‖ - 1), norm_nonneg y]

/-- Absorption of one factor `e^{-S/(4a)}` with weight `B P` and `P ≤ 2B²`. -/
lemma gv_main1 (u η T P : ℝ) (hT : 0 ≤ T) (hTle : T ≤ Real.exp (-(1 / 9) * (u ^ 2 + η ^ 2)))
    (hP : P ≤ 2 * (1 + |u| + |η|) ^ 2) :
    (1 + |u| + |η|) * P * T ≤ 2 * latticeW gradAlpha gradK u η := by
  have hB1 : (1 : ℝ) ≤ 1 + |u| + |η| := by linarith [abs_nonneg u, abs_nonneg η]
  have hB0 : (0 : ℝ) ≤ 1 + |u| + |η| := by linarith
  rw [gv_L_eq]
  calc (1 + |u| + |η|) * P * T ≤ (1 + |u| + |η|) * (2 * (1 + |u| + |η|) ^ 2) * T :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hP hB0) hT
    _ = 2 * (1 + |u| + |η|) ^ 3 * T := by ring
    _ ≤ 2 * (1 + |u| + |η|) ^ 3 * Real.exp (-(1 / 9) * (u ^ 2 + η ^ 2)) :=
        mul_le_mul_of_nonneg_left hTle (by positivity)
    _ ≤ 2 * (1 + |u| + |η|) ^ 12 * Real.exp (-(1 / 9) * (u ^ 2 + η ^ 2)) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hB1 (by norm_num : (3:ℕ) ≤ 12)) (by norm_num))
          (Real.exp_pos _).le
    _ = 2 * ((1 + |u| + |η|) ^ 12 * Real.exp (-(1 / 9) * (u ^ 2 + η ^ 2))) := by ring

/-- Absorption of one factor `e^{-S/(4a)}` with weight `B P` and `P ≤ 4B⁴`. -/
lemma gv_main2 (u η T P : ℝ) (hT : 0 ≤ T) (hTle : T ≤ Real.exp (-(1 / 9) * (u ^ 2 + η ^ 2)))
    (hP : P ≤ 4 * (1 + |u| + |η|) ^ 4) :
    (1 + |u| + |η|) * P * T ≤ 4 * latticeW gradAlpha gradK u η := by
  have hB1 : (1 : ℝ) ≤ 1 + |u| + |η| := by linarith [abs_nonneg u, abs_nonneg η]
  have hB0 : (0 : ℝ) ≤ 1 + |u| + |η| := by linarith
  rw [gv_L_eq]
  calc (1 + |u| + |η|) * P * T ≤ (1 + |u| + |η|) * (4 * (1 + |u| + |η|) ^ 4) * T :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hP hB0) hT
    _ = 4 * (1 + |u| + |η|) ^ 5 * T := by ring
    _ ≤ 4 * (1 + |u| + |η|) ^ 5 * Real.exp (-(1 / 9) * (u ^ 2 + η ^ 2)) :=
        mul_le_mul_of_nonneg_left hTle (by positivity)
    _ ≤ 4 * (1 + |u| + |η|) ^ 12 * Real.exp (-(1 / 9) * (u ^ 2 + η ^ 2)) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hB1 (by norm_num : (5:ℕ) ≤ 12)) (by norm_num))
          (Real.exp_pos _).le
    _ = 4 * ((1 + |u| + |η|) ^ 12 * Real.exp (-(1 / 9) * (u ^ 2 + η ^ 2))) := by ring

/-- Constant absorption: `X ≤ 4L` gives `X ≤ 4(1+K)L` for `K, L ≥ 0`. -/
lemma gv_le_C (K X L : ℝ) (hK : 0 ≤ K) (hL : 0 ≤ L) (h : X ≤ 4 * L) :
    X ≤ 4 * (1 + K) * L := by
  nlinarith [mul_nonneg hK hL]

theorem gradVjBounds : ∃ C : ℝ, 0 ≤ C ∧ ∀ (ν s : ℝ) (j : ℤ) (x : ℝ × ℝ), 0 < ν → ν ≤ 1 → 0 < s → s ≤ (11 / 10) / ν → ∀ a b : Fin 2, (1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|) * ‖Vj ν s j x‖ ≤ C * gradW ν x j ∧ (1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|) * ‖fderiv ℝ (Vj ν s j) x (ei a)‖ ≤ C * gradW ν x j ∧ (1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|) * ‖fderiv ℝ (fun y => fderiv ℝ (Vj ν s j) y (ei a)) x (ei b)‖ ≤ C * gradW ν x j := by
  obtain ⟨K2, hK2, hK2b⟩ := hessVjUnif
  refine ⟨4 * (1 + K2), by linarith, ?_⟩
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
  have hP2 : (1 + sq2 (xj ν j x)) ^ 2 ≤ 4 * (1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|) ^ 4 := by
    have h := pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ 1 + sq2 (xj ν j x)) hP1 2
    calc (1 + sq2 (xj ν j x)) ^ 2 ≤ (2 * (1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|) ^ 2) ^ 2 := h
      _ = 4 * (1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|) ^ 4 := by ring
  have hL0 : 0 ≤ latticeW gradAlpha gradK (x.1 - (j : ℝ) * cOf ν) x.2 := by
    unfold latticeW
    exact mul_nonneg (by positivity) (Real.exp_pos _).le
  -- the norm of `V_j`
  have hVnorm : ‖Vj ν s j x‖ = hsE ν s j x * ‖xj ν j x‖ := by
    have hVeq : Vj ν s j x = hsE ν s j x • Jrot (xj ν j x) := rfl
    rw [hVeq, hs_smul_jrot, abs_of_nonneg hE0]
  have hV : (1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|) * ‖Vj ν s j x‖
      ≤ 2 * latticeW gradAlpha gradK (x.1 - (j : ℝ) * cOf ν) x.2 := by
    have c1 : hsE ν s j x * ‖xj ν j x‖ ≤ Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) * (1 + sq2 (xj ν j x)) :=
      mul_le_mul hEle hnx hn0 hT0
    have c2 : (1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|) * ‖Vj ν s j x‖
        ≤ (1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|) *
          (Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) * (1 + sq2 (xj ν j x))) := by
      rw [hVnorm]
      exact mul_le_mul_of_nonneg_left c1 hB0
    have hm := gv_main1 (x.1 - (j : ℝ) * cOf ν) x.2 _ _ hT0 hTle hP1
    calc _ ≤ _ := c2
      _ = (1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|) * (1 + sq2 (xj ν j x)) *
            Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) := by ring
      _ ≤ _ := hm
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
    have hX : |hsE ν s j x * hsL ν s j a x| * ‖xj ν j x‖ ≤ Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) * sq2 (xj ν j x) := by
      rw [abs_mul, abs_of_nonneg hE0]
      have hX1 : hsE ν s j x * |hsL ν s j a x| ≤ Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) * (‖xj ν j x‖ / ageA ν s) :=
        mul_le_mul hEle hA (abs_nonneg _) hT0
      have hX2 : ‖xj ν j x‖ / ageA ν s * ‖xj ν j x‖ ≤ sq2 (xj ν j x) := by
        calc ‖xj ν j x‖ / ageA ν s * ‖xj ν j x‖ ≤ ‖xj ν j x‖ * ‖xj ν j x‖ :=
              mul_le_mul_of_nonneg_right (div_le_self hn0 ha1) hn0
          _ = ‖xj ν j x‖ ^ 2 := by ring
          _ ≤ sq2 (xj ν j x) := hu_norm_sq_le _
      calc hsE ν s j x * |hsL ν s j a x| * ‖xj ν j x‖
          ≤ Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) * (‖xj ν j x‖ / ageA ν s) * ‖xj ν j x‖ :=
            mul_le_mul_of_nonneg_right hX1 hn0
        _ = Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) * (‖xj ν j x‖ / ageA ν s * ‖xj ν j x‖) := by ring
        _ ≤ Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) * sq2 (xj ν j x) :=
            mul_le_mul_of_nonneg_left hX2 hT0
    have hE1 : hsE ν s j x * 1 ≤ Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) := by
      rw [mul_one]; exact hEle
    calc ‖hsG ν s j a x‖ ≤ hsE ν s j x * 1 + |hsE ν s j x * hsL ν s j a x| * ‖xj ν j x‖ := hG1
      _ ≤ Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) + Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) * sq2 (xj ν j x) :=
            add_le_add hE1 hX
      _ = Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) * (1 + sq2 (xj ν j x)) := by ring
  have hV2 : (1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|) * ‖fderiv ℝ (Vj ν s j) x (ei a)‖
      ≤ 2 * latticeW gradAlpha gradK (x.1 - (j : ℝ) * cOf ν) x.2 := by
    have hm := gv_main1 (x.1 - (j : ℝ) * cOf ν) x.2 _ _ hT0 hTle hP1
    calc _ ≤ (1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|) *
            (Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) * (1 + sq2 (xj ν j x))) :=
          mul_le_mul_of_nonneg_left hG hB0
      _ = (1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|) * (1 + sq2 (xj ν j x)) *
            Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) := by ring
      _ ≤ _ := hm
  -- the second derivative
  have hD2 := hK2b ν s hν hν1 hs hs1 j x b a
  have hD2' : (1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|) * ‖fderiv ℝ (fun y => fderiv ℝ (Vj ν s j) y (ei a)) x (ei b)‖
      ≤ 4 * (1 + K2) * latticeW gradAlpha gradK (x.1 - (j : ℝ) * cOf ν) x.2 := by
    have hm := gv_main2 (x.1 - (j : ℝ) * cOf ν) x.2 _ _ hT0 hTle hP2
    have hL0' := hL0
    calc _ ≤ (1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|) *
            (K2 * ((1 + sq2 (xj ν j x)) ^ 2 * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)))) :=
          mul_le_mul_of_nonneg_left hD2 hB0
      _ = K2 * ((1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|) * (1 + sq2 (xj ν j x)) ^ 2 *
            Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s))) := by ring
      _ ≤ K2 * (4 * latticeW gradAlpha gradK (x.1 - (j : ℝ) * cOf ν) x.2) :=
          mul_le_mul_of_nonneg_left hm hK2
      _ ≤ 4 * (1 + K2) * latticeW gradAlpha gradK (x.1 - (j : ℝ) * cOf ν) x.2 := by
          nlinarith [mul_nonneg hK2 hL0']
  refine ⟨?_, ?_, ?_⟩
  · exact gv_le_C K2 _ _ hK2 hL0 (le_trans hV (by linarith))
  · exact gv_le_C K2 _ _ hK2 hL0 (le_trans hV2 (by linarith))
  · exact hD2'

end UnforcedLeray.Short.PartIIIb.Concrete
