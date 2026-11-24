import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_inst_10_4
import UnforcedLeray.Short.PartIIIb.Sub.Leaves.EAcHessUnif
import UnforcedLeray.Short.PartIIIb.Sub.Leaves.EAcMgradUnif
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.HpPsiTermSummable.Gauss
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.FATermSummable

/-!
# `PartIII-b:C/inst/10/4` leaf D: locally uniform Gaussian domination of the lattice terms
(source 4963-4972, 4978, 5063-5079)

The second-derivative and meridional-gradient bounds of `Sub/Leaves/EAcHessUnif.lean` and
`Sub/Leaves/EAcMgradUnif.lean` use only `a = ageA ν s ≥ 1`, so they hold for every `ν > 0`, `s > 0`
(the proofs are reused verbatim below). The Gaussian factor is then dominated, uniformly for
`s ∈ [s0, s1]` and `‖x‖ ≤ R`, by `K · exp(-(j c)²/(16 P))`, which is summable in `j`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The common majorant `(1+|x_j|²)² e^{-|x_j|²/(4a)}`. -/
def td_domG (ν s : ℝ) (j : ℤ) (x : ℝ × ℝ) : ℝ :=
  (1 + sq2 (xj ν j x)) ^ 2 * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s))

/-- Second derivatives of `V_j` (body of `hessVjUnif`, valid for all `ν > 0`, `s > 0`). -/
theorem td_hess (ν s : ℝ) (hν : 0 < ν) (hs : 0 < s) (j : ℤ) (x : ℝ × ℝ) (p b : Fin 2) :
    ‖fderiv ℝ (fun y => fderiv ℝ (Vj ν s j) y (ei b)) x (ei p)‖ ≤ 4 * td_domG ν s j x := by
  unfold td_domG
  have ha : 0 < ageA ν s := by unfold ageA; nlinarith [mul_pos hν hs]
  have ha1 : 1 ≤ ageA ν s := by unfold ageA; nlinarith [mul_pos hν hs]
  have hfun : (fun y => fderiv ℝ (Vj ν s j) y (ei b)) = hsG ν s j b :=
    funext fun y => hs_eq ν s j b y
  rw [hfun, gp_fderiv_line (hsG ν s j b) x (ei p) (hs_diff ν s j b x), (hs_line ν s j b p x).deriv]
  have hκ : 0 ≤ (ageA ν s ^ 2)⁻¹ := by positivity
  have hE0 : 0 ≤ Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) := (Real.exp_pos _).le
  have hE0' : 0 ≤ hsE ν s j x := mul_nonneg hκ hE0
  have hn0 : 0 ≤ ‖xj ν j x‖ := norm_nonneg _
  have hA : |hsL ν s j p x| ≤ ‖xj ν j x‖ / ageA ν s :=
    (gp_c1_abs (xj ν j x) (ei p) (ageA ν s) ha).trans
      (div_le_div_of_nonneg_right (mul_le_of_le_one_right hn0 (hs_ei_norm_le p)) ha.le)
  have hB : |hsL ν s j b x| ≤ ‖xj ν j x‖ / ageA ν s :=
    (gp_c1_abs (xj ν j x) (ei b) (ageA ν s) ha).trans
      (div_le_div_of_nonneg_right (mul_le_of_le_one_right hn0 (hs_ei_norm_le b)) ha.le)
  have hC : |hsLp ν s b p| ≤ 1 / ageA ν s := by
    unfold hsLp
    refine (gp_c1_abs (ei p) (ei b) (ageA ν s) ha).trans
      (div_le_div_of_nonneg_right ?_ ha.le)
    nlinarith [hs_ei_norm_le p, hs_ei_norm_le b, norm_nonneg (ei p), norm_nonneg (ei b)]
  have hPp := hs_Pp_bound ((ageA ν s ^ 2)⁻¹) (Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)))
    (hsL ν s j p x) ‖xj ν j x‖ (ageA ν s) hκ hE0 ha hA
  have hS := hs_scalar' (hsE ν s j x) _ (hsL ν s j b x) (hsLp ν s b p) ‖xj ν j x‖ (ageA ν s)
    (ei b) (ei p) (hs_ei_norm_le b) (hs_ei_norm_le p) hE0' hn0 ha hPp hB hC
  have hX := hu_poly_bound ‖xj ν j x‖ (ageA ν s) (1 + sq2 (xj ν j x)) (sq2 (xj ν j x))
    hn0 ha1 (hu_sq2_nonneg _) (hu_norm_sq_le _) rfl
  have hcoef : hsE ν s j x ≤ Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) := by
    unfold hsE
    have hinv : (ageA ν s ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith)
    exact mul_le_of_le_one_left hE0 hinv
  have hF : hsE ν s j x * (3 * ‖xj ν j x‖ / ageA ν s + ‖xj ν j x‖ ^ 3 / ageA ν s ^ 2) ≤
      Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) *
        (4 * (1 + sq2 (xj ν j x)) ^ 2) := by
    calc hsE ν s j x * (3 * ‖xj ν j x‖ / ageA ν s + ‖xj ν j x‖ ^ 3 / ageA ν s ^ 2)
        ≤ hsE ν s j x * (4 * (1 + sq2 (xj ν j x)) ^ 2) :=
          mul_le_mul_of_nonneg_left hX hE0'
      _ ≤ Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) * (4 * (1 + sq2 (xj ν j x)) ^ 2) :=
          mul_le_mul_of_nonneg_right hcoef (by positivity)
  refine le_trans (hs_vec_bound _ _ _ _ _ _) (le_trans hS ?_)
  calc hsE ν s j x * (3 * ‖xj ν j x‖ / ageA ν s + ‖xj ν j x‖ ^ 3 / ageA ν s ^ 2)
      ≤ Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) * (4 * (1 + sq2 (xj ν j x)) ^ 2) := hF
    _ = 4 * ((1 + sq2 (xj ν j x)) ^ 2 * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s))) := by ring

/-- Meridional gradient of `p_j` (body of `mgradPjUnif`, valid for all `ν > 0`, `s > 0`). -/
theorem td_mgrad (ν s : ℝ) (hν : 0 < ν) (hs : 0 < s) (j : ℤ) (x : ℝ × ℝ) :
    ‖mgrad (pj ν s j) x‖ ≤ 2 * td_domG ν s j x := by
  unfold td_domG
  have ha : 0 < ageA ν s := by unfold ageA; nlinarith [mul_pos hν hs]
  have ha1 : 1 ≤ ageA ν s := by unfold ageA; nlinarith [mul_pos hν hs]
  have hmain := mg_mgrad_bound ν s ha j x
  have hn0 : 0 ≤ ‖xj ν j x‖ := norm_nonneg _
  have hQ : 0 ≤ sq2 (xj ν j x) := mu_sq2_nonneg _
  have hk3 : (ageA ν s ^ 3)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ ha1)
  have hE : Real.exp (-(sq2 (xj ν j x)) / (2 * ageA ν s))
      ≤ Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) := by
    apply Real.exp_le_exp.mpr
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith [mul_nonneg hQ ha.le]
  have hA : 2 * ‖xj ν j x‖ / ageA ν s ≤ 2 * ‖xj ν j x‖ := div_le_self (by positivity) ha1
  have hnonneg : 0 ≤ 2 * ‖xj ν j x‖ / ageA ν s := div_nonneg (by positivity) ha.le
  have hE4 : 0 ≤ Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) := (Real.exp_pos _).le
  have h1 : (ageA ν s ^ 3)⁻¹ * (Real.exp (-(sq2 (xj ν j x)) / (2 * ageA ν s)) *
      (2 * ‖xj ν j x‖ / ageA ν s))
      ≤ 1 * (Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) * (2 * ‖xj ν j x‖)) :=
    mul_le_mul hk3 (mul_le_mul hE hA hnonneg hE4)
      (mul_nonneg (Real.exp_pos _).le hnonneg) zero_le_one
  have hn2 := mu_norm_sq_le (xj ν j x)
  have hnS2 : ‖xj ν j x‖ ≤ (1 + sq2 (xj ν j x)) ^ 2 := by
    nlinarith [sq_nonneg (‖xj ν j x‖ - 1 / 2), hn2, hQ, sq_nonneg (sq2 (xj ν j x))]
  have h3 := mul_le_mul_of_nonneg_right hnS2 hE4
  calc ‖mgrad (pj ν s j) x‖
      ≤ (ageA ν s ^ 3)⁻¹ * (Real.exp (-(sq2 (xj ν j x)) / (2 * ageA ν s)) *
          (2 * ‖xj ν j x‖ / ageA ν s)) := hmain
    _ ≤ 1 * (Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) * (2 * ‖xj ν j x‖)) := h1
    _ = 2 * (‖xj ν j x‖ * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s))) := by ring
    _ ≤ 2 * ((1 + sq2 (xj ν j x)) ^ 2 * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s))) := by
        nlinarith [h3]

theorem td_frob_nonneg (A : Mat3) : 0 ≤ frob A := by
  unfold frob
  exact Real.sqrt_nonneg _

theorem td_abs_entry (A : Mat3) (i k : Fin 3) : |A i k| ≤ frob A := by
  unfold frob
  rw [← Real.sqrt_sq_eq_abs]
  apply Real.sqrt_le_sqrt
  have h1 : A i k ^ 2 ≤ ∑ l, A i l ^ 2 :=
    Finset.single_le_sum (f := fun l => A i l ^ 2) (fun l _ => sq_nonneg _) (Finset.mem_univ k)
  have h2 : ∑ l, A i l ^ 2 ≤ ∑ m, ∑ l, A m l ^ 2 :=
    Finset.single_le_sum (f := fun m => ∑ l, A m l ^ 2)
      (fun m _ => Finset.sum_nonneg fun l _ => sq_nonneg _) (Finset.mem_univ i)
  linarith

theorem td_sum_B (A : Mat3) : ∑ i, ∑ j, |A i j| ≤ 9 * frob A := by
  simp only [Fin.sum_univ_three]
  linarith [td_abs_entry A 0 0, td_abs_entry A 0 1, td_abs_entry A 0 2,
    td_abs_entry A 1 0, td_abs_entry A 1 1, td_abs_entry A 1 2,
    td_abs_entry A 2 0, td_abs_entry A 2 1, td_abs_entry A 2 2]

theorem td_sum_M (C : Mat3) : ∑ i, ∑ j, |C i j + C j i| ≤ 18 * frob C := by
  have hM : ∀ i k : Fin 3, |C i k + C k i| ≤ 2 * frob C := fun i k => by
    have := abs_add_le (C i k) (C k i)
    linarith [td_abs_entry C i k, td_abs_entry C k i]
  simp only [Fin.sum_univ_three]
  linarith [hM 0 0, hM 0 1, hM 0 2, hM 1 0, hM 1 1, hM 1 2, hM 2 0, hM 2 1, hM 2 2]

theorem td_sum_two (C : Mat3) : ∑ a : Fin 2, ∑ b : Fin 2, |C (mi a) (mi b)| ≤ 4 * frob C := by
  simp only [Fin.sum_univ_two]
  linarith [td_abs_entry C (mi 0) (mi 0), td_abs_entry C (mi 0) (mi 1),
    td_abs_entry C (mi 1) (mi 0), td_abs_entry C (mi 1) (mi 1)]

/-- The pointwise bound of `V_j`. -/
theorem td_vj_norm (ν s : ℝ) (ha1 : 1 ≤ ageA ν s) (j : ℤ) (x : ℝ × ℝ) :
    ‖Vj ν s j x‖ ≤ td_domG ν s j x := by
  unfold Vj td_domG
  have hE : 0 ≤ Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) := (Real.exp_pos _).le
  have hκ : |(ageA ν s ^ 2)⁻¹ * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s))|
      ≤ Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) := by
    rw [abs_of_nonneg (mul_nonneg (inv_nonneg.mpr (sq_nonneg _)) hE)]
    exact mul_le_of_le_one_left hE (inv_le_one_of_one_le₀ (one_le_pow₀ ha1))
  have hn1 : ‖xj ν j x‖ ≤ 1 + sq2 (xj ν j x) := by
    nlinarith [hu_norm_sq_le (xj ν j x), sq_nonneg (‖xj ν j x‖ - 1), hu_sq2_nonneg (xj ν j x)]
  have hn2 : 1 + sq2 (xj ν j x) ≤ (1 + sq2 (xj ν j x)) ^ 2 := by
    nlinarith [hu_sq2_nonneg (xj ν j x)]
  rw [norm_smul, gp_jrot_norm, Real.norm_eq_abs]
  calc |(ageA ν s ^ 2)⁻¹ * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s))| * ‖xj ν j x‖
      ≤ Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) * ‖xj ν j x‖ :=
        mul_le_mul_of_nonneg_right hκ (norm_nonneg _)
    _ ≤ Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) * (1 + sq2 (xj ν j x)) ^ 2 :=
        mul_le_mul_of_nonneg_left (hn1.trans hn2) hE
    _ = (1 + sq2 (xj ν j x)) ^ 2 * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) := by ring

/-- Elementary inequality behind the absorption of the polynomial weight. -/
theorem td_quad (Pm y : ℝ) (hPm : 0 < Pm) (hy : 0 ≤ y) :
    (1 + 8 * Pm * y) ^ 2 ≤ (1 + 16 * Pm + 128 * Pm ^ 2) * Real.exp y := by
  have h1 : y + 1 ≤ Real.exp y := Real.add_one_le_exp y
  have h2 : 1 + y + y ^ 2 / 2 ≤ Real.exp y := Real.quadratic_le_exp_of_nonneg hy
  have h0 : 1 ≤ Real.exp y := Real.one_le_exp hy
  have hy2 : y ^ 2 ≤ 2 * Real.exp y := by nlinarith
  have hye : y ≤ Real.exp y := by linarith
  have e1 : 16 * Pm * y ≤ 16 * Pm * Real.exp y :=
    mul_le_mul_of_nonneg_left hye (by nlinarith)
  have e2 : 64 * Pm ^ 2 * y ^ 2 ≤ 64 * Pm ^ 2 * (2 * Real.exp y) :=
    mul_le_mul_of_nonneg_left hy2 (by positivity)
  nlinarith [e1, e2, h0]

/-- Uniform Gaussian majorant of `(1+|x_j|²)² e^{-|x_j|²/(4a)}` for `1 ≤ a ≤ P` and `‖x‖ ≤ R`. -/
theorem td_gauss (ν s R Pm : ℝ) (hPm : 0 < Pm) (ha1 : 1 ≤ ageA ν s) (haP : ageA ν s ≤ Pm)
    (x : ℝ × ℝ) (hx : ‖x‖ ≤ R) (j : ℤ) :
    td_domG ν s j x ≤ (1 + 16 * Pm + 128 * Pm ^ 2) * Real.exp (R ^ 2 / (8 * Pm)) *
      Real.exp (-(1 / (16 * Pm)) * ((j : ℝ) * cOf ν) ^ 2) := by
  unfold td_domG
  have ha : 0 < ageA ν s := by linarith
  have hPm0 : Pm ≠ 0 := hPm.ne'
  have htt : sq2 (xj ν j x) = (x.1 - (j : ℝ) * cOf ν) ^ 2 + x.2 ^ 2 := by
    simp [sq2, xj]
  have ht0 : 0 ≤ sq2 (xj ν j x) := hu_sq2_nonneg _
  have hR0 : 0 ≤ R := (norm_nonneg x).trans hx
  have hx1 : |x.1| ≤ R := (norm_fst_le x).trans hx
  have hx1sq : x.1 ^ 2 ≤ R ^ 2 := by nlinarith [sq_abs x.1, abs_nonneg x.1]
  have ht_ge : (((j : ℝ) * cOf ν) ^ 2) / 2 - R ^ 2 ≤ sq2 (xj ν j x) := by
    rw [htt]
    nlinarith [sq_nonneg (2 * x.1 - (j : ℝ) * cOf ν), sq_nonneg x.2]
  -- exponential bound
  have hE1 : Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s))
      ≤ Real.exp (-(sq2 (xj ν j x)) / (4 * Pm)) := by
    apply Real.exp_le_exp.mpr
    rw [neg_div, neg_div]
    have h := div_le_div_of_nonneg_left ht0 (by linarith : (0:ℝ) < 4 * ageA ν s)
      (by linarith : 4 * ageA ν s ≤ 4 * Pm)
    linarith
  have hsplit : Real.exp (-(sq2 (xj ν j x)) / (4 * Pm))
      = Real.exp (-(sq2 (xj ν j x) / (8 * Pm))) * Real.exp (-(sq2 (xj ν j x) / (8 * Pm))) := by
    rw [← Real.exp_add]
    congr 1
    field_simp
    ring
  have hy0 : 0 ≤ sq2 (xj ν j x) / (8 * Pm) := div_nonneg ht0 (by linarith)
  have hquad : (1 + sq2 (xj ν j x)) ^ 2 ≤
      (1 + 16 * Pm + 128 * Pm ^ 2) * Real.exp (sq2 (xj ν j x) / (8 * Pm)) := by
    have := td_quad Pm (sq2 (xj ν j x) / (8 * Pm)) hPm hy0
    have e : 1 + 8 * Pm * (sq2 (xj ν j x) / (8 * Pm)) = 1 + sq2 (xj ν j x) := by
      field_simp
    rw [e] at this
    exact this
  have hB : (1 + sq2 (xj ν j x)) ^ 2 * Real.exp (-(sq2 (xj ν j x) / (8 * Pm)))
      ≤ 1 + 16 * Pm + 128 * Pm ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_right hquad (Real.exp_pos (-(sq2 (xj ν j x) / (8 * Pm)))).le
    have h2 : Real.exp (sq2 (xj ν j x) / (8 * Pm)) * Real.exp (-(sq2 (xj ν j x) / (8 * Pm))) = 1 := by
      rw [← Real.exp_add]
      simp
    calc (1 + sq2 (xj ν j x)) ^ 2 * Real.exp (-(sq2 (xj ν j x) / (8 * Pm)))
        ≤ (1 + 16 * Pm + 128 * Pm ^ 2) * Real.exp (sq2 (xj ν j x) / (8 * Pm))
            * Real.exp (-(sq2 (xj ν j x) / (8 * Pm))) := h1
      _ = (1 + 16 * Pm + 128 * Pm ^ 2) * (Real.exp (sq2 (xj ν j x) / (8 * Pm))
            * Real.exp (-(sq2 (xj ν j x) / (8 * Pm)))) := by ring
      _ = 1 + 16 * Pm + 128 * Pm ^ 2 := by rw [h2, mul_one]
  have hE3 : Real.exp (-(sq2 (xj ν j x) / (8 * Pm)))
      ≤ Real.exp (R ^ 2 / (8 * Pm)) * Real.exp (-(1 / (16 * Pm)) * ((j : ℝ) * cOf ν) ^ 2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hdiv : (((j : ℝ) * cOf ν) ^ 2 / 2 - R ^ 2) / (8 * Pm)
        ≤ sq2 (xj ν j x) / (8 * Pm) := div_le_div_of_nonneg_right ht_ge (by linarith)
    have e4 : (((j : ℝ) * cOf ν) ^ 2 / 2 - R ^ 2) / (8 * Pm)
        = -(R ^ 2 / (8 * Pm) + -(1 / (16 * Pm)) * ((j : ℝ) * cOf ν) ^ 2) := by
      field_simp
      ring
    linarith
  have hK : 0 ≤ 1 + 16 * Pm + 128 * Pm ^ 2 := by nlinarith
  calc (1 + sq2 (xj ν j x)) ^ 2 * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s))
      ≤ (1 + sq2 (xj ν j x)) ^ 2 * Real.exp (-(sq2 (xj ν j x)) / (4 * Pm)) :=
        mul_le_mul_of_nonneg_left hE1 (by positivity)
    _ = ((1 + sq2 (xj ν j x)) ^ 2 * Real.exp (-(sq2 (xj ν j x) / (8 * Pm)))) *
          Real.exp (-(sq2 (xj ν j x) / (8 * Pm))) := by rw [hsplit]; ring
    _ ≤ (1 + 16 * Pm + 128 * Pm ^ 2) * Real.exp (-(sq2 (xj ν j x) / (8 * Pm))) :=
        mul_le_mul_of_nonneg_right hB (Real.exp_pos _).le
    _ ≤ (1 + 16 * Pm + 128 * Pm ^ 2) * (Real.exp (R ^ 2 / (8 * Pm)) *
          Real.exp (-(1 / (16 * Pm)) * ((j : ℝ) * cOf ν) ^ 2)) :=
        mul_le_mul_of_nonneg_left hE3 hK
    _ = (1 + 16 * Pm + 128 * Pm ^ 2) * Real.exp (R ^ 2 / (8 * Pm)) *
          Real.exp (-(1 / (16 * Pm)) * ((j : ℝ) * cOf ν) ^ 2) := by ring

/-- Matrix-term bound: the `j`-th term is bounded by `(36 + 32|ν|)(|B| + |C|) · td_domG`. -/
theorem td_eABt (ν s : ℝ) (hν : 0 < ν) (hs : 0 < s) (B C : Mat3) (x : ℝ × ℝ) (j : ℤ) :
    ‖eABt ν s B C x j‖ ≤ (36 + 32 * |ν|) * (frob B + frob C) * td_domG ν s j x := by
  have ha1 : 1 ≤ ageA ν s := by unfold ageA; nlinarith [mul_pos hν hs]
  have hG0 : 0 ≤ td_domG ν s j x := by unfold td_domG; positivity
  have hfB := td_frob_nonneg B
  have hfC := td_frob_nonneg C
  have hV := td_vj_norm ν s ha1 j x
  have hMV1 : ‖mv B (emb (Vj ν s j x))‖ ≤ 9 * frob B * td_domG ν s j x :=
    (fa_mv_norm_le B _).trans (mul_le_mul (td_sum_B B) ((fa_emb_norm_le _).trans hV)
      (norm_nonneg _) (mul_nonneg (by norm_num) hfB))
  have hT1 : ‖(2 : ℝ) • mv B (emb (Vj ν s j x))‖ ≤ 2 * (9 * frob B * td_domG ν s j x) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0:ℝ) < 2)]
    exact mul_le_mul_of_nonneg_left hMV1 (by norm_num)
  have hH : ‖hessContr C (Vj ν s j) x‖ ≤ 16 * frob C * td_domG ν s j x := by
    have step : ‖hessContr C (Vj ν s j) x‖ ≤
        (∑ a : Fin 2, ∑ b : Fin 2, |C (mi a) (mi b)|) * (4 * td_domG ν s j x) := by
      unfold hessContr
      refine (fa_emb_norm_le _).trans ?_
      rw [Finset.sum_mul]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
      rw [Finset.sum_mul]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (td_hess ν s hν hs j x a b) (abs_nonneg _)
    refine step.trans ?_
    calc (∑ a : Fin 2, ∑ b : Fin 2, |C (mi a) (mi b)|) * (4 * td_domG ν s j x)
        ≤ (4 * frob C) * (4 * td_domG ν s j x) :=
          mul_le_mul_of_nonneg_right (td_sum_two C) (by linarith)
      _ = 16 * frob C * td_domG ν s j x := by ring
  have hMG : ‖mv (fun a b => C a b + C b a) (emb (mgrad (pj ν s j) x))‖
      ≤ 36 * frob C * td_domG ν s j x := by
    have h1 := fa_mv_norm_le (fun a b => C a b + C b a) (emb (mgrad (pj ν s j) x))
    have h2 : ‖emb (mgrad (pj ν s j) x)‖ ≤ 2 * td_domG ν s j x :=
      (fa_emb_norm_le _).trans (td_mgrad ν s hν hs j x)
    have h3 := td_sum_M C
    calc ‖mv (fun a b => C a b + C b a) (emb (mgrad (pj ν s j) x))‖
        ≤ (∑ i, ∑ j, |C i j + C j i|) * ‖emb (mgrad (pj ν s j) x)‖ := h1
      _ ≤ (18 * frob C) * (2 * td_domG ν s j x) :=
          mul_le_mul h3 h2 (norm_nonneg _) (by linarith)
      _ = 36 * frob C * td_domG ν s j x := by ring
  unfold eABt
  calc ‖(2 : ℝ) • mv B (emb (Vj ν s j x)) + (2 * ν) • hessContr C (Vj ν s j) x
        - mv (fun a b => C a b + C b a) (emb (mgrad (pj ν s j) x))‖
      ≤ ‖(2 : ℝ) • mv B (emb (Vj ν s j x))‖ + ‖(2 * ν) • hessContr C (Vj ν s j) x‖ +
        ‖mv (fun a b => C a b + C b a) (emb (mgrad (pj ν s j) x))‖ :=
        (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ 2 * (9 * frob B * td_domG ν s j x) + |2 * ν| * (16 * frob C * td_domG ν s j x)
          + 36 * frob C * td_domG ν s j x := by
        refine add_le_add (add_le_add hT1 ?_) hMG
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left hH (abs_nonneg _)
    _ ≤ (36 + 32 * |ν|) * (frob B + frob C) * td_domG ν s j x := by
        rw [abs_mul, abs_two]
        nlinarith [mul_nonneg hfB hG0, mul_nonneg hfC hG0,
          mul_nonneg (mul_nonneg (abs_nonneg ν) hfB) hG0,
          mul_nonneg (mul_nonneg (abs_nonneg ν) hfC) hG0]

/-- Leaf D (source 4978, 5063-5079): locally uniform Gaussian domination. -/
theorem eaTermDomLeaf : EAcTermDomLeaf := by
  intro ν hν s0 s1 R hs0
  obtain ⟨Pm, hPmd⟩ : ∃ P : ℝ, P = 1 + ν * |s1| := ⟨_, rfl⟩
  have hPm : 0 < Pm := by
    rw [hPmd]
    nlinarith [mul_nonneg hν.le (abs_nonneg s1)]
  have hc : 0 < cOf ν := by
    unfold cOf
    exact inv_pos.mpr (pow_pos hν 2)
  have hα : (0:ℝ) < 1 / (16 * Pm) := div_pos one_pos (by linarith)
  have hsum : Summable (fun j : ℤ => Real.exp (-(1 / (16 * Pm)) * ((j : ℝ) * cOf ν) ^ 2)) := by
    refine (gp_gauss_summable 0 (1 / (16 * Pm)) (cOf ν) hα hc).congr (fun j => ?_)
    congr 1
    ring
  refine ⟨fun j => (36 + 32 * |ν|) * (1 + 16 * Pm + 128 * Pm ^ 2) * Real.exp (R ^ 2 / (8 * Pm)) *
      Real.exp (-(1 / (16 * Pm)) * ((j : ℝ) * cOf ν) ^ 2), hsum.mul_left _, ?_⟩
  intro s hs0s hss1 x hx B C j
  have hsp : 0 < s := lt_of_lt_of_le hs0 hs0s
  have ha1 : 1 ≤ ageA ν s := by unfold ageA; nlinarith [mul_pos hν hsp]
  have haP : ageA ν s ≤ Pm := by
    rw [hPmd]
    unfold ageA
    nlinarith [le_abs_self s1, mul_le_mul_of_nonneg_left (hss1.trans (le_abs_self s1)) hν.le]
  have hG := td_eABt ν s hν hsp B C x j
  have hD := td_gauss ν s R Pm hPm ha1 haP x hx j
  have hK0 : 0 ≤ (36 + 32 * |ν|) * (frob B + frob C) :=
    mul_nonneg (by positivity) (add_nonneg (td_frob_nonneg B) (td_frob_nonneg C))
  calc ‖eABt ν s B C x j‖ ≤ (36 + 32 * |ν|) * (frob B + frob C) * td_domG ν s j x := hG
    _ ≤ (36 + 32 * |ν|) * (frob B + frob C) * ((1 + 16 * Pm + 128 * Pm ^ 2) *
          Real.exp (R ^ 2 / (8 * Pm)) * Real.exp (-(1 / (16 * Pm)) * ((j : ℝ) * cOf ν) ^ 2)) :=
        mul_le_mul_of_nonneg_left hD hK0
    _ = (frob B + frob C) * ((36 + 32 * |ν|) * (1 + 16 * Pm + 128 * Pm ^ 2) *
          Real.exp (R ^ 2 / (8 * Pm)) * Real.exp (-(1 / (16 * Pm)) * ((j : ℝ) * cOf ν) ^ 2)) := by
        ring

end UnforcedLeray.Short.PartIIIb.Concrete

end
