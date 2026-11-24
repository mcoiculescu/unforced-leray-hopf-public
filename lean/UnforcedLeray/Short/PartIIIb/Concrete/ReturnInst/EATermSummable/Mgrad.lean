import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_inst_3

/-!
# `C/inst/3` leaf 2: the meridional gradient of `p_j` (source 4964-4966, 4978)

`p_j = -a⁻³ e^{-|x_j|²/(2a)}`; its meridional gradient is bounded by
`K (1+|q-jc|)³ e^{-(q-jc)²/(4a)}`.
-/

set_option autoImplicit false

noncomputable section

open Real

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The basis vectors `ei` have sup norm at most one. -/
lemma mg_ei_norm_le (p : Fin 2) : ‖ei p‖ ≤ 1 := by
  fin_cases p <;> simp [ei, Prod.norm_def]

/-- Line derivative of the Gaussian weight `exp(-|x_j|²/(2a))`. -/
lemma mg_exp2_line (ν s : ℝ) (j : ℤ) (x v : ℝ × ℝ) :
    HasDerivAt (fun t : ℝ => Real.exp (-(sq2 (xj ν j (x + t • v))) / (2 * ageA ν s)))
      (Real.exp (-(sq2 (xj ν j x)) / (2 * ageA ν s)) *
        (-(2 * (xj ν j x).1 * v.1 + 2 * (xj ν j x).2 * v.2) / (2 * ageA ν s))) 0 := by
  have h := (((gp_sq2_line ν j x v).neg).div_const (2 * ageA ν s)).exp
  convert h using 2
  · simp
  · simp [neg_div]

/-- Line derivative of `p_j`. -/
lemma mg_pj_line (ν s : ℝ) (j : ℤ) (x v : ℝ × ℝ) :
    HasDerivAt (fun t : ℝ => pj ν s j (x + t • v))
      (-((ageA ν s ^ 3)⁻¹ * (Real.exp (-(sq2 (xj ν j x)) / (2 * ageA ν s)) *
        (-(2 * (xj ν j x).1 * v.1 + 2 * (xj ν j x).2 * v.2) / (2 * ageA ν s))))) 0 := by
  have h := ((mg_exp2_line ν s j x v).const_mul ((ageA ν s ^ 3)⁻¹)).neg
  exact h

/-- Directional derivative of `p_j`. -/
lemma mg_fderiv_pj (ν s : ℝ) (j : ℤ) (x v : ℝ × ℝ) :
    fderiv ℝ (pj ν s j) x v =
      -((ageA ν s ^ 3)⁻¹ * (Real.exp (-(sq2 (xj ν j x)) / (2 * ageA ν s)) *
        (-(2 * (xj ν j x).1 * v.1 + 2 * (xj ν j x).2 * v.2) / (2 * ageA ν s)))) := by
  have hd : DifferentiableAt ℝ (pj ν s j) x := by
    unfold pj xj sq2
    fun_prop
  rw [gp_fderiv_line (pj ν s j) x v hd]
  exact (mg_pj_line ν s j x v).deriv

/-- Coefficient bound: `|-(2 y·v)/(2a)| ≤ 2 ‖y‖ ‖v‖ / a`. -/
lemma mg_c2_abs (y v : ℝ × ℝ) (a : ℝ) (ha : 0 < a) :
    |-(2 * y.1 * v.1 + 2 * y.2 * v.2) / (2 * a)| ≤ 2 * ‖y‖ * ‖v‖ / a := by
  have h1 : |y.1| ≤ ‖y‖ := by rw [← Real.norm_eq_abs]; exact norm_fst_le y
  have h2 : |y.2| ≤ ‖y‖ := by rw [← Real.norm_eq_abs]; exact norm_snd_le y
  have h3 : |v.1| ≤ ‖v‖ := by rw [← Real.norm_eq_abs]; exact norm_fst_le v
  have h4 : |v.2| ≤ ‖v‖ := by rw [← Real.norm_eq_abs]; exact norm_snd_le v
  have p1 : |y.1 * v.1| ≤ ‖y‖ * ‖v‖ := by
    rw [abs_mul]; exact mul_le_mul h1 h3 (abs_nonneg _) (norm_nonneg _)
  have p2 : |y.2 * v.2| ≤ ‖y‖ * ‖v‖ := by
    rw [abs_mul]; exact mul_le_mul h2 h4 (abs_nonneg _) (norm_nonneg _)
  have hS : |2 * y.1 * v.1 + 2 * y.2 * v.2| ≤ 4 * (‖y‖ * ‖v‖) := by
    have e : 2 * y.1 * v.1 + 2 * y.2 * v.2 = 2 * (y.1 * v.1) + 2 * (y.2 * v.2) := by ring
    rw [e]
    calc |2 * (y.1 * v.1) + 2 * (y.2 * v.2)| ≤ |2 * (y.1 * v.1)| + |2 * (y.2 * v.2)| :=
          abs_add_le _ _
      _ = 2 * |y.1 * v.1| + 2 * |y.2 * v.2| := by
          simp only [abs_mul, abs_two]
      _ ≤ 4 * (‖y‖ * ‖v‖) := by linarith
  have h2a : 0 < 2 * a := by linarith
  rw [abs_div, abs_neg, abs_of_pos h2a, div_le_div_iff₀ h2a ha]
  nlinarith [mul_le_mul_of_nonneg_right hS ha.le]

/-- Componentwise bound on the meridional gradient of `p_j`. -/
lemma mg_comp_bound (ν s : ℝ) (ha : 0 < ageA ν s) (j : ℤ) (x : ℝ × ℝ) (p : Fin 2) :
    |fderiv ℝ (pj ν s j) x (ei p)| ≤
      (ageA ν s ^ 3)⁻¹ * (Real.exp (-(sq2 (xj ν j x)) / (2 * ageA ν s)) *
        (2 * ‖xj ν j x‖ / ageA ν s)) := by
  have hκ : 0 ≤ (ageA ν s ^ 3)⁻¹ := by positivity
  have hE0 : 0 ≤ Real.exp (-(sq2 (xj ν j x)) / (2 * ageA ν s)) := (Real.exp_pos _).le
  have hc : |-(2 * (xj ν j x).1 * (ei p).1 + 2 * (xj ν j x).2 * (ei p).2) / (2 * ageA ν s)|
      ≤ 2 * ‖xj ν j x‖ / ageA ν s := by
    refine (mg_c2_abs _ _ _ ha).trans ?_
    have hn := mg_ei_norm_le p
    have hu := norm_nonneg (xj ν j x)
    apply div_le_div_of_nonneg_right _ ha.le
    nlinarith [mul_nonneg hu (sub_nonneg.mpr hn)]
  rw [mg_fderiv_pj, abs_neg, abs_mul, abs_mul, abs_of_nonneg hκ, abs_of_nonneg hE0]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hc hE0) hκ

/-- The gradient norm before the Gaussian comparison. -/
lemma mg_mgrad_bound (ν s : ℝ) (ha : 0 < ageA ν s) (j : ℤ) (x : ℝ × ℝ) :
    ‖mgrad (pj ν s j) x‖ ≤
      (ageA ν s ^ 3)⁻¹ * (Real.exp (-(sq2 (xj ν j x)) / (2 * ageA ν s)) *
        (2 * ‖xj ν j x‖ / ageA ν s)) := by
  unfold mgrad
  rw [Prod.norm_def]
  refine max_le ?_ ?_
  · show ‖fderiv ℝ (pj ν s j) x (ei 0)‖ ≤ _
    rw [Real.norm_eq_abs]
    exact mg_comp_bound ν s ha j x 0
  · show ‖fderiv ℝ (pj ν s j) x (ei 1)‖ ≤ _
    rw [Real.norm_eq_abs]
    exact mg_comp_bound ν s ha j x 1

/-- The Gaussian weight of `p_j` is dominated by the one in the first coordinate. -/
lemma mg_exp2_le (ν s : ℝ) (ha : 0 < ageA ν s) (j : ℤ) (x : ℝ × ℝ) :
    Real.exp (-(sq2 (xj ν j x)) / (2 * ageA ν s))
      ≤ Real.exp (-(1 / (4 * ageA ν s)) * (x.1 - (j : ℝ) * cOf ν) ^ 2) := by
  apply Real.exp_le_exp.mpr
  have hsq : sq2 (xj ν j x) = (x.1 - (j : ℝ) * cOf ν) ^ 2 + x.2 ^ 2 := rfl
  have e : -(sq2 (xj ν j x)) / (2 * ageA ν s) = -(1 / (2 * ageA ν s)) * sq2 (xj ν j x) := by
    ring
  have hBA : 1 / (4 * ageA ν s) ≤ 1 / (2 * ageA ν s) :=
    one_div_le_one_div_of_le (by linarith) (by linarith)
  have hA : 0 ≤ 1 / (2 * ageA ν s) := by positivity
  rw [e, hsq]
  nlinarith [mul_nonneg (sub_nonneg.mpr hBA) (sq_nonneg (x.1 - (j : ℝ) * cOf ν)),
    mul_nonneg hA (sq_nonneg x.2)]

/-- Main leaf: the meridional gradient of `p_j` is a polynomial times a Gaussian. -/
theorem mgradPjBound : MgradPjBound := by
  intro ν s ha x
  refine ⟨(ageA ν s ^ 3)⁻¹ * (2 / ageA ν s) * (1 + |x.2|) ^ 3, fun j => ?_⟩
  have hmain := mg_mgrad_bound ν s ha j x
  have hE := mg_exp2_le ν s ha j x
  have hn0 : 0 ≤ ‖xj ν j x‖ := norm_nonneg _
  have h1 := gp_one_add_norm ν j x
  have h2 : (1 + ‖xj ν j x‖) ^ 3 ≤ ((1 + |x.2|) * (1 + |x.1 - (j : ℝ) * cOf ν|)) ^ 3 :=
    pow_le_pow_left₀ (by positivity) h1 3
  have h3 : ‖xj ν j x‖ ≤ (1 + ‖xj ν j x‖) ^ 3 := by
    nlinarith [pow_nonneg hn0 2, pow_nonneg hn0 3]
  have hnM : ‖xj ν j x‖ ≤ (1 + |x.2|) ^ 3 * (1 + |x.1 - (j : ℝ) * cOf ν|) ^ 3 := by
    calc ‖xj ν j x‖ ≤ (1 + ‖xj ν j x‖) ^ 3 := h3
      _ ≤ ((1 + |x.2|) * (1 + |x.1 - (j : ℝ) * cOf ν|)) ^ 3 := h2
      _ = (1 + |x.2|) ^ 3 * (1 + |x.1 - (j : ℝ) * cOf ν|) ^ 3 := by ring
  have key : Real.exp (-(sq2 (xj ν j x)) / (2 * ageA ν s)) * ‖xj ν j x‖ ≤
      Real.exp (-(1 / (4 * ageA ν s)) * (x.1 - (j : ℝ) * cOf ν) ^ 2) *
        ((1 + |x.2|) ^ 3 * (1 + |x.1 - (j : ℝ) * cOf ν|) ^ 3) :=
    mul_le_mul hE hnM hn0 (Real.exp_pos _).le
  calc ‖mgrad (pj ν s j) x‖
      ≤ (ageA ν s ^ 3)⁻¹ * (Real.exp (-(sq2 (xj ν j x)) / (2 * ageA ν s)) *
          (2 * ‖xj ν j x‖ / ageA ν s)) := hmain
    _ = ((ageA ν s ^ 3)⁻¹ * (2 / ageA ν s)) *
          (Real.exp (-(sq2 (xj ν j x)) / (2 * ageA ν s)) * ‖xj ν j x‖) := by ring
    _ ≤ ((ageA ν s ^ 3)⁻¹ * (2 / ageA ν s)) *
          (Real.exp (-(1 / (4 * ageA ν s)) * (x.1 - (j : ℝ) * cOf ν) ^ 2) *
            ((1 + |x.2|) ^ 3 * (1 + |x.1 - (j : ℝ) * cOf ν|) ^ 3)) :=
        mul_le_mul_of_nonneg_left key (by positivity)
    _ = ((ageA ν s ^ 3)⁻¹ * (2 / ageA ν s) * (1 + |x.2|) ^ 3) *
          ((1 + |x.1 - (j : ℝ) * cOf ν|) ^ 3 *
            Real.exp (-(1 / (4 * ageA ν s)) * (x.1 - (j : ℝ) * cOf ν) ^ 2)) := by ring

end UnforcedLeray.Short.PartIIIb.Concrete
