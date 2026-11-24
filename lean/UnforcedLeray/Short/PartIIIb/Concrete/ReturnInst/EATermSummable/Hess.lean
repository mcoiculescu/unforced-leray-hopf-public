import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_inst_3

/-!
# `C/inst/3` leaf 1: second derivatives of `V_j` (source 4963-4966, 4978)

`V_j = (a²)⁻¹ e^{-|x_j|²/(4a)} J x_j`.  By `gp_fderiv_Vj` the first derivative in a fixed
direction `b` is an explicit function `hsG ν s j b`; its derivative in direction `p` is computed
along the line (product rule), and bounded by `K (1+|q-jc|)³ e^{-(q-jc)²/(4a)}`.
-/

set_option autoImplicit false

noncomputable section

open Real

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Scalar prefactor `(a²)⁻¹ e^{-|x_j|²/(4a)}` of `V_j`. -/
def hsE (ν s : ℝ) (j : ℤ) (y : ℝ × ℝ) : ℝ :=
  (ageA ν s ^ 2)⁻¹ * Real.exp (-(sq2 (xj ν j y)) / (4 * ageA ν s))

/-- Coefficient `-(2 (x_j · e_b))/(4a)`. -/
def hsL (ν s : ℝ) (j : ℤ) (b : Fin 2) (y : ℝ × ℝ) : ℝ :=
  -(2 * (xj ν j y).1 * (ei b).1 + 2 * (xj ν j y).2 * (ei b).2) / (4 * ageA ν s)

/-- Constant coefficient `-(2 (e_p · e_b))/(4a)` (the derivative of `hsL` in direction `p`). -/
def hsLp (ν s : ℝ) (b p : Fin 2) : ℝ :=
  -(2 * (ei p).1 * (ei b).1 + 2 * (ei p).2 * (ei b).2) / (4 * ageA ν s)

/-- The explicit first derivative `y ↦ fderiv V_j y (e_b)`. -/
def hsG (ν s : ℝ) (j : ℤ) (b : Fin 2) (y : ℝ × ℝ) : ℝ × ℝ :=
  hsE ν s j y • Jrot (ei b) + (hsE ν s j y * hsL ν s j b y) • Jrot (xj ν j y)

/-- The basis vectors have sup norm at most one. -/
lemma hs_ei_norm_le (p : Fin 2) : ‖ei p‖ ≤ 1 := by
  fin_cases p <;> simp [ei, Prod.norm_def]

/-- Norm of `c • Jrot w`. -/
lemma hs_smul_jrot (c : ℝ) (w : ℝ × ℝ) : ‖c • Jrot w‖ = |c| * ‖w‖ := by
  rw [norm_smul, gp_jrot_norm, Real.norm_eq_abs]

/-- Triangle inequality for the three-term vector sum. -/
lemma hs_vec_bound (c1 c2 c3 : ℝ) (w1 w2 w3 : ℝ × ℝ) :
    ‖c1 • Jrot w1 + (c2 • Jrot w2 + c3 • Jrot w3)‖ ≤
      |c1| * ‖w1‖ + (|c2| * ‖w2‖ + |c3| * ‖w3‖) := by
  calc ‖c1 • Jrot w1 + (c2 • Jrot w2 + c3 • Jrot w3)‖
      ≤ ‖c1 • Jrot w1‖ + ‖c2 • Jrot w2 + c3 • Jrot w3‖ := norm_add_le _ _
    _ ≤ ‖c1 • Jrot w1‖ + (‖c2 • Jrot w2‖ + ‖c3 • Jrot w3‖) :=
        add_le_add le_rfl (norm_add_le _ _)
    _ = |c1| * ‖w1‖ + (|c2| * ‖w2‖ + |c3| * ‖w3‖) := by
        rw [hs_smul_jrot c1 w1, hs_smul_jrot c2 w2, hs_smul_jrot c3 w3]

/-- `hsG` is differentiable. -/
lemma hs_diff (ν s : ℝ) (j : ℤ) (b : Fin 2) (x : ℝ × ℝ) :
    DifferentiableAt ℝ (hsG ν s j b) x := by
  unfold hsG hsE hsL xj Jrot sq2
  fun_prop

/-- The explicit form of `fderiv V_j` in the direction `e_b`. -/
lemma hs_eq (ν s : ℝ) (j : ℤ) (b : Fin 2) (y : ℝ × ℝ) :
    fderiv ℝ (Vj ν s j) y (ei b) = hsG ν s j b y := by
  rw [gp_fderiv_Vj]
  simp only [hsG, hsE, hsL, mul_assoc]

/-- Line derivative of `hsG` in direction `e_p` at `x`. -/
lemma hs_line (ν s : ℝ) (j : ℤ) (b p : Fin 2) (x : ℝ × ℝ) :
    HasDerivAt (fun t : ℝ => hsG ν s j b (x + t • ei p))
      (((ageA ν s ^ 2)⁻¹ * (Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) * hsL ν s j p x)) • Jrot (ei b)
        + ((hsE ν s j x * hsL ν s j b x) • Jrot (ei p)
          + ((ageA ν s ^ 2)⁻¹ * (Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) * hsL ν s j p x)
              * hsL ν s j b x + hsE ν s j x * hsLp ν s b p) • Jrot (xj ν j x))) 0 := by
  have hP : HasDerivAt (fun t : ℝ => hsE ν s j (x + t • ei p))
      ((ageA ν s ^ 2)⁻¹ * (Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) * hsL ν s j p x)) 0 :=
    (gp_exp_line ν s j x (ei p)).const_mul ((ageA ν s ^ 2)⁻¹)
  have hX : HasDerivAt (fun t : ℝ => (xj ν j (x + t • ei p)).1) (ei p).1 0 := by
    have h : HasDerivAt (fun t : ℝ => x.1 + t * (ei p).1 - (j : ℝ) * cOf ν) (ei p).1 0 := by
      have h0 := (((hasDerivAt_id' (0:ℝ)).mul_const (ei p).1).const_add x.1).sub_const
        ((j : ℝ) * cOf ν)
      simpa using h0
    exact h
  have hY : HasDerivAt (fun t : ℝ => (xj ν j (x + t • ei p)).2) (ei p).2 0 := by
    have h : HasDerivAt (fun t : ℝ => x.2 + t * (ei p).2) (ei p).2 0 := by
      have h0 := ((hasDerivAt_id' (0:ℝ)).mul_const (ei p).2).const_add x.2
      simpa using h0
    exact h
  have hL : HasDerivAt (fun t : ℝ => hsL ν s j b (x + t • ei p)) (hsLp ν s b p) 0 := by
    unfold hsL hsLp
    have h := ((((hX.const_mul 2).mul_const (ei b).1).add
      ((hY.const_mul 2).mul_const (ei b).2)).neg.div_const (4 * ageA ν s))
    exact h
  have hJ : HasDerivAt (fun t : ℝ => Jrot (xj ν j (x + t • ei p))) (Jrot (ei p)) 0 := by
    have e1 : HasDerivAt (fun t : ℝ => -(xj ν j (x + t • ei p)).2) (-(ei p).2) 0 := hY.neg
    exact e1.prodMk hX
  have hfin := (hP.smul_const (Jrot (ei b))).add ((hP.mul hL).smul hJ)
  refine hfin.congr_deriv ?_
  simp only [zero_smul, add_zero, Pi.mul_apply]

/-- Real inequality: the derivative coefficient of `P` in direction `p`. -/
lemma hs_Pp_bound (κ E A n a : ℝ) (hκ : 0 ≤ κ) (hE : 0 ≤ E) (ha : 0 < a)
    (hA : |A| ≤ n / a) : |κ * (E * A)| ≤ κ * E * (n / a) := by
  rw [abs_mul, abs_of_nonneg hκ, abs_mul, abs_of_nonneg hE]
  calc κ * (E * |A|) = κ * E * |A| := by ring
    _ ≤ κ * E * (n / a) := mul_le_mul_of_nonneg_left hA (mul_nonneg hκ hE)

/-- Real inequality: the scalar part of the line derivative. -/
lemma hs_scalar' (P0 Pp B C n a : ℝ) (w1 w2 : ℝ × ℝ) (hw1 : ‖w1‖ ≤ 1) (hw2 : ‖w2‖ ≤ 1)
    (hP0 : 0 ≤ P0) (hn : 0 ≤ n) (ha : 0 < a) (hPp : |Pp| ≤ P0 * (n / a))
    (hB : |B| ≤ n / a) (hC : |C| ≤ 1 / a) :
    |Pp| * ‖w1‖ + (|P0 * B| * ‖w2‖ + |Pp * B + P0 * C| * n)
      ≤ P0 * (3 * n / a + n ^ 3 / a ^ 2) := by
  have e1 : |Pp| * ‖w1‖ ≤ |Pp| := mul_le_of_le_one_right (abs_nonneg _) hw1
  have e2 : |P0 * B| * ‖w2‖ ≤ |P0 * B| := mul_le_of_le_one_right (abs_nonneg _) hw2
  have h1 : |P0 * B| ≤ P0 * (n / a) := by
    rw [abs_mul, abs_of_nonneg hP0]
    exact mul_le_mul_of_nonneg_left hB hP0
  have h2 : |Pp * B + P0 * C| ≤ P0 * (n / a) * (n / a) + P0 * (1 / a) := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg hP0]
    exact add_le_add (mul_le_mul hPp hB (abs_nonneg _) (mul_nonneg hP0 (div_nonneg hn ha.le)))
      (mul_le_mul_of_nonneg_left hC hP0)
  have h3 : |Pp * B + P0 * C| * n ≤ (P0 * (n / a) * (n / a) + P0 * (1 / a)) * n :=
    mul_le_mul_of_nonneg_right h2 hn
  have h4 : |P0 * B| + |Pp * B + P0 * C| * n ≤ P0 * (n / a) + (P0 * (n / a) * (n / a) + P0 * (1 / a)) * n := by
    linarith
  calc |Pp| * ‖w1‖ + (|P0 * B| * ‖w2‖ + |Pp * B + P0 * C| * n)
      ≤ |Pp| + (|P0 * B| + |Pp * B + P0 * C| * n) := by linarith
    _ ≤ P0 * (n / a) + (P0 * (n / a) + (P0 * (n / a) * (n / a) + P0 * (1 / a)) * n) := by
        linarith
    _ = P0 * (3 * n / a + n ^ 3 / a ^ 2) := by ring

/-- Real inequality: summing the polynomial coefficient. -/
lemma hs_X_bound (n a M : ℝ) (hn : 0 ≤ n) (ha : 0 < a) (hnM : n ≤ M) (hn3 : n ^ 3 ≤ M) :
    3 * n / a + n ^ 3 / a ^ 2 ≤ (3 / a + 1 / a ^ 2) * M := by
  have ha3 : 0 ≤ 3 / a := div_nonneg (by norm_num) ha.le
  have ha2 : 0 ≤ 1 / a ^ 2 := div_nonneg zero_le_one (pow_nonneg ha.le 2)
  calc 3 * n / a + n ^ 3 / a ^ 2 = (3 / a) * n + (1 / a ^ 2) * n ^ 3 := by ring
    _ ≤ (3 / a) * M + (1 / a ^ 2) * M :=
        add_le_add (mul_le_mul_of_nonneg_left hnM ha3) (mul_le_mul_of_nonneg_left hn3 ha2)
    _ = (3 / a + 1 / a ^ 2) * M := by ring

/-- Leaf 1: second derivatives of `V_j` (source 4963-4966, 4978). -/
theorem hessVjBound : HessVjBound := by
  intro ν s ha x
  refine ⟨(ageA ν s ^ 2)⁻¹ * (3 / ageA ν s + 1 / ageA ν s ^ 2) * (1 + |x.2|) ^ 3,
    fun j p b => ?_⟩
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
  have hM : (1 + ‖xj ν j x‖) ^ 3 ≤ (1 + |x.2|) ^ 3 * (1 + |x.1 - (j : ℝ) * cOf ν|) ^ 3 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (gp_one_add_norm ν j x) 3
  have h3 : ‖xj ν j x‖ ≤ (1 + ‖xj ν j x‖) ^ 3 := by
    nlinarith [pow_nonneg hn0 2, pow_nonneg hn0 3]
  have hnM : ‖xj ν j x‖ ≤ (1 + |x.2|) ^ 3 * (1 + |x.1 - (j : ℝ) * cOf ν|) ^ 3 := h3.trans hM
  have hn3M : ‖xj ν j x‖ ^ 3 ≤ (1 + |x.2|) ^ 3 * (1 + |x.1 - (j : ℝ) * cOf ν|) ^ 3 :=
    (pow_le_pow_left₀ hn0 (by linarith : ‖xj ν j x‖ ≤ 1 + ‖xj ν j x‖) 3).trans hM
  have hS := hs_scalar' (hsE ν s j x) _ (hsL ν s j b x) (hsLp ν s b p) ‖xj ν j x‖ (ageA ν s)
    (ei b) (ei p) (hs_ei_norm_le b) (hs_ei_norm_le p) hE0' hn0 ha hPp hB hC
  have hEb : hsE ν s j x ≤ (ageA ν s ^ 2)⁻¹ *
      Real.exp (-(1 / (4 * ageA ν s)) * (x.1 - (j : ℝ) * cOf ν) ^ 2) := by
    unfold hsE
    exact mul_le_mul_of_nonneg_left (gp_exp_le ν s ha j x) hκ
  have hX := hs_X_bound ‖xj ν j x‖ (ageA ν s) _ hn0 ha hnM hn3M
  have hF : hsE ν s j x * (3 * ‖xj ν j x‖ / ageA ν s + ‖xj ν j x‖ ^ 3 / ageA ν s ^ 2) ≤
      (ageA ν s ^ 2)⁻¹ * (3 / ageA ν s + 1 / ageA ν s ^ 2) * (1 + |x.2|) ^ 3 *
        ((1 + |x.1 - (j : ℝ) * cOf ν|) ^ 3 *
          Real.exp (-(1 / (4 * ageA ν s)) * (x.1 - (j : ℝ) * cOf ν) ^ 2)) := by
    have hX0 : 0 ≤ 3 * ‖xj ν j x‖ / ageA ν s + ‖xj ν j x‖ ^ 3 / ageA ν s ^ 2 := by positivity
    calc hsE ν s j x * (3 * ‖xj ν j x‖ / ageA ν s + ‖xj ν j x‖ ^ 3 / ageA ν s ^ 2)
        ≤ ((ageA ν s ^ 2)⁻¹ * Real.exp (-(1 / (4 * ageA ν s)) * (x.1 - (j : ℝ) * cOf ν) ^ 2)) *
            (3 * ‖xj ν j x‖ / ageA ν s + ‖xj ν j x‖ ^ 3 / ageA ν s ^ 2) :=
          mul_le_mul_of_nonneg_right hEb hX0
      _ ≤ ((ageA ν s ^ 2)⁻¹ * Real.exp (-(1 / (4 * ageA ν s)) * (x.1 - (j : ℝ) * cOf ν) ^ 2)) *
            ((3 / ageA ν s + 1 / ageA ν s ^ 2) *
              ((1 + |x.2|) ^ 3 * (1 + |x.1 - (j : ℝ) * cOf ν|) ^ 3)) :=
          mul_le_mul_of_nonneg_left hX (by positivity)
      _ = (ageA ν s ^ 2)⁻¹ * (3 / ageA ν s + 1 / ageA ν s ^ 2) * (1 + |x.2|) ^ 3 *
            ((1 + |x.1 - (j : ℝ) * cOf ν|) ^ 3 *
              Real.exp (-(1 / (4 * ageA ν s)) * (x.1 - (j : ℝ) * cOf ν) ^ 2)) := by ring
  refine le_trans (hs_vec_bound _ _ _ _ _ _) (le_trans hS hF)

end UnforcedLeray.Short.PartIIIb.Concrete
