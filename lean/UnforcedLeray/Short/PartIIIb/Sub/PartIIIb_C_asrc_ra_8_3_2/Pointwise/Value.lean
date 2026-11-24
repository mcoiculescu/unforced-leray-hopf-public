import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_8_3_2.EnvL2
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.HpPsiTermSummable.Gauss

set_option autoImplicit false

noncomputable section

open Set Real

namespace UnforcedLeray.Short.PartIIIb.Concrete

lemma pw_abs_le_frob (M : Mat3) (i j : Fin 3) : |M i j| ≤ frob M := by
  unfold frob
  have h1 : M i j ^ 2 ≤ ∑ j', M i j' ^ 2 :=
    Finset.single_le_sum (f := fun j' => M i j' ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
  have h2 : ∑ j', M i j' ^ 2 ≤ ∑ i', ∑ j', M i' j' ^ 2 :=
    Finset.single_le_sum (f := fun i' => ∑ j', M i' j' ^ 2)
      (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  exact Real.abs_le_sqrt (h1.trans h2)

lemma pw_S_le_frob (M : Mat3) :
    |M 0 0| + |M 0 2| + |M 2 0| + |M 2 2| ≤ 4 * frob M := by
  have := pw_abs_le_frob M 0 0
  have := pw_abs_le_frob M 0 2
  have := pw_abs_le_frob M 2 0
  have := pw_abs_le_frob M 2 2
  linarith

lemma pw_norm_sq_le_sq2 (y : ℝ × ℝ) : ‖y‖ ^ 2 ≤ sq2 y := by
  have hn : ‖y‖ = max |y.1| |y.2| := by
    rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
  unfold sq2
  rcases max_choice |y.1| |y.2| with h | h <;> rw [hn, h] <;>
    nlinarith [sq_abs y.1, sq_abs y.2, sq_nonneg y.1, sq_nonneg y.2]

lemma pw_exp_le (a : ℝ) (ha : 0 < a) (ha9 : a ≤ 9 / 4) (y : ℝ × ℝ) :
    Real.exp (-(sq2 y) / (4 * a)) ≤ Real.exp (-(‖y‖ ^ 2) / 9) := by
  apply Real.exp_le_exp.2
  have h1 : ‖y‖ ^ 2 / 9 ≤ ‖y‖ ^ 2 / (4 * a) :=
    div_le_div_of_nonneg_left (sq_nonneg _) (by linarith) (by linarith)
  have h2 : ‖y‖ ^ 2 / (4 * a) ≤ sq2 y / (4 * a) :=
    div_le_div_of_nonneg_right (pw_norm_sq_le_sq2 y) (by linarith)
  have e1 : -(sq2 y) / (4 * a) = -(sq2 y / (4 * a)) := neg_div _ _
  have e2 : -(‖y‖ ^ 2) / 9 = -(‖y‖ ^ 2 / 9) := neg_div _ _
  rw [e1, e2]
  linarith

/-- Pointwise value bound of one lattice term, with the full Gaussian. -/
lemma pw_T_value (ν s : ℝ) (ha : 0 < ageA ν s) (hb : 1 ≤ ageA ν s) (ha9 : ageA ν s ≤ 9 / 4)
    (M : Mat3) (x : ℝ × ℝ) (j : ℤ) :
    ‖merApply M (Vj ν s j x) - fderiv ℝ (Vj ν s j) x (merApply M (xj ν j x))‖ ≤
      12 * frob M * ((1 + ‖xj ν j x‖) ^ 4 * Real.exp (-(‖xj ν j x‖ ^ 2) / 9)) := by
  have hn0 : 0 ≤ ‖xj ν j x‖ := norm_nonneg _
  have hE0 : 0 ≤ Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) := (Real.exp_pos _).le
  have hκ1 : (ageA ν s ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hb)
  have hκ0 : 0 ≤ (ageA ν s ^ 2)⁻¹ := inv_nonneg.2 (sq_nonneg _)
  have hS0 : 0 ≤ |M 0 0| + |M 0 2| + |M 2 0| + |M 2 2| := by positivity
  have hS := pw_S_le_frob M
  have h1 := gp_merApply_norm_le M (Vj ν s j x)
  have h2 := gp_fderiv_Vj_norm ν s ha j x (merApply M (xj ν j x))
  have h3 := gp_merApply_norm_le M (xj ν j x)
  rw [gp_Vj_norm_eq] at h1
  have hE := pw_exp_le (ageA ν s) ha ha9 (xj ν j x)
  have h2' := h2.trans (mul_le_mul_of_nonneg_left h3
    (mul_nonneg (mul_nonneg hκ0 hE0) (add_nonneg zero_le_one (div_nonneg (sq_nonneg _) ha.le))))
  refine (norm_sub_le _ _).trans ?_
  refine (add_le_add h1 h2').trans ?_
  generalize Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) = E at *
  generalize (ageA ν s ^ 2)⁻¹ = κ at *
  generalize ‖xj ν j x‖ = n at *
  generalize |M 0 0| + |M 0 2| + |M 2 0| + |M 2 2| = S at *
  generalize frob M = F at *
  generalize Real.exp (-(n ^ 2) / 9) = Q at *
  generalize ageA ν s = a at *
  have hpa : 0 ≤ n ^ 2 := sq_nonneg n
  have hκE : κ * E ≤ E := mul_le_of_le_one_left hE0 hκ1
  have hT1 : κ * E * (1 + n ^ 2 / a) ≤ E * (1 + n ^ 2) :=
    (mul_le_mul_of_nonneg_right hκE (add_nonneg zero_le_one (div_nonneg hpa ha.le))).trans
      (mul_le_mul_of_nonneg_left (by
        have : n ^ 2 / a ≤ n ^ 2 := by
          rw [div_eq_mul_inv]; exact mul_le_of_le_one_right hpa (inv_le_one_of_one_le₀ hb)
        linarith) hE0)
  have hA : S * (κ * E * n) ≤ S * (E * n) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hκE hn0) hS0
  have hB : κ * E * (1 + n ^ 2 / a) * (S * n) ≤ E * (1 + n ^ 2) * (S * n) :=
    mul_le_mul_of_nonneg_right hT1 (mul_nonneg hS0 hn0)
  have hC : S * (E * n) + E * (1 + n ^ 2) * (S * n) = S * E * (2 * n + n ^ 3) := by ring
  have hQ0 : 0 ≤ Q := hE0.trans hE
  have hD : S * E * (2 * n + n ^ 3) ≤ S * Q * (2 * n + n ^ 3) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hE hS0)
      (add_nonneg (by linarith) (pow_nonneg hn0 3))
  have hP : 2 * n + n ^ 3 ≤ 3 * (1 + n) ^ 4 := by
    nlinarith [pow_nonneg hn0 3, pow_nonneg hn0 4, pow_nonneg hn0 2]
  have hE' : S * Q * (2 * n + n ^ 3) ≤ (4 * F) * Q * (3 * (1 + n) ^ 4) :=
    mul_le_mul (mul_le_mul_of_nonneg_right hS hQ0) hP
      (add_nonneg (by linarith) (pow_nonneg hn0 3)) (mul_nonneg (by linarith) hQ0)
  calc S * (κ * E * n) + κ * E * (1 + n ^ 2 / a) * (S * n)
      ≤ S * (E * n) + E * (1 + n ^ 2) * (S * n) := add_le_add hA hB
    _ = S * E * (2 * n + n ^ 3) := hC
    _ ≤ S * Q * (2 * n + n ^ 3) := hD
    _ ≤ (4 * F) * Q * (3 * (1 + n) ^ 4) := hE'
    _ = 12 * F * ((1 + n) ^ 4 * Q) := by ring

/-- Summable majorant of the lattice envelope summands. -/
lemma pw_G_summable (ν : ℝ) (hν : 0 < ν) (x : ℝ × ℝ) :
    Summable (fun j : ℤ => (1 + ‖xj ν j x‖) ^ 4 * Real.exp (-(‖xj ν j x‖ ^ 2) / 9)) := by
  have hc : 0 < cOf ν := inv_pos.2 (pow_pos hν 2)
  have hS := gp_gauss_summable x.1 (1 / 18) (cOf ν) (by norm_num) hc
  refine Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_) (hS.mul_left 5200)
  have h := gEnv_summand_le (norm_nonneg (xj ν j x))
  have h1 : |(xj ν j x).1| ≤ ‖xj ν j x‖ := norm_fst_le (xj ν j x)
  have hsq : (x.1 - (j : ℝ) * cOf ν) ^ 2 ≤ ‖xj ν j x‖ ^ 2 := by
    have e : (x.1 - (j : ℝ) * cOf ν) ^ 2 = |(xj ν j x).1| ^ 2 := by
      rw [sq_abs]; rfl
    rw [e]
    exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  have hexp : Real.exp (-(‖xj ν j x‖ ^ 2) / 18) ≤ Real.exp (-(1 / 18) * (x.1 - (j : ℝ) * cOf ν) ^ 2) :=
    Real.exp_le_exp.2 (by linarith)
  calc (1 + ‖xj ν j x‖) ^ 4 * Real.exp (-(‖xj ν j x‖ ^ 2) / 9)
      ≤ 5200 * Real.exp (-(‖xj ν j x‖ ^ 2) / 18) := h
    _ ≤ 5200 * Real.exp (-(1 / 18) * (x.1 - (j : ℝ) * cOf ν) ^ 2) :=
        mul_le_mul_of_nonneg_left hexp (by norm_num)

/-- Pointwise bound of `h^p_A`: the value part. -/
lemma pw_hpA_value (ν : ℝ) (χ : ℝ → ℝ) (A : ℝ → Mat3) (s : ℝ) (x : ℝ × ℝ)
    (hν : 0 < ν) (hs : 0 < s) (hs1 : s ≤ (11 / 10) / ν) :
    ‖hpA ν χ A s x‖ ≤ 12 * frob (Ay ν χ A s) * gEnv ν x := by
  have hνs : ν * s ≤ 11 / 10 := by
    have := (le_div_iff₀ hν).1 hs1
    linarith
  have ha : 0 < ageA ν s := by unfold ageA; nlinarith [mul_pos hν hs]
  have hb : 1 ≤ ageA ν s := by unfold ageA; nlinarith [mul_pos hν hs]
  have ha9 : ageA ν s ≤ 9 / 4 := by unfold ageA; linarith
  have hsum := pw_G_summable ν hν x
  have hT : Summable (fun j : ℤ => ‖merApply (Ay ν χ A s) (Vj ν s j x)
      - fderiv ℝ (Vj ν s j) x (merApply (Ay ν χ A s) (xj ν j x))‖) :=
    Summable.of_nonneg_of_le (fun j => norm_nonneg _)
      (fun j => pw_T_value ν s ha hb ha9 (Ay ν χ A s) x j) (hsum.mul_left _)
  unfold hpA gEnv
  calc ‖∑' j : ℤ, (merApply (Ay ν χ A s) (Vj ν s j x)
        - fderiv ℝ (Vj ν s j) x (merApply (Ay ν χ A s) (xj ν j x)))‖
      ≤ ∑' j : ℤ, ‖merApply (Ay ν χ A s) (Vj ν s j x)
        - fderiv ℝ (Vj ν s j) x (merApply (Ay ν χ A s) (xj ν j x))‖ := norm_tsum_le_tsum_norm hT
    _ ≤ ∑' j : ℤ, 12 * frob (Ay ν χ A s) * ((1 + ‖xj ν j x‖) ^ 4 * Real.exp (-(‖xj ν j x‖ ^ 2) / 9)) :=
        hT.tsum_le_tsum (fun j => pw_T_value ν s ha hb ha9 (Ay ν χ A s) x j) ((hsum.mul_left _))
    _ = 12 * frob (Ay ν χ A s) * ∑' j : ℤ, (1 + ‖xj ν j x‖) ^ 4 * Real.exp (-(‖xj ν j x‖ ^ 2) / 9) :=
        tsum_mul_left

end UnforcedLeray.Short.PartIIIb.Concrete
