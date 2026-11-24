import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_1_2.Vj

/-!
# `PartIII-b:C/grad/3/4/1/1/2/2`: s-derivative bounds of `V_j`

Source `the November 2 reference manuscript`
4963-4980, 5036-5039, 5063-5079.

With `a = 1 + ν t`, `V_j(t) = P(t) • J x_j` where `P(t) = (a²)⁻¹ e^{-|x_j|²/(4a)}`; its derivative
is `vsEd • J x_j` with `vsEd = ν e^{-S/(4a)} (-2a⁻³ + S a⁻⁴/4)`, `S = |x_j|²`.  The t-derivative of
`fderiv V_j x (e_a) = hsG ν t j a x` is obtained by the product rule from `vsEd` and
`hsL' = -(2 (x_j · e_a))'/(4a)`.  Using `ν s ≤ 11/10`, `1 ≤ a ≤ 21/10` and `S ≤ B²` for
`B = 1 + |x_j,1| + |x_j,2|`, every term is absorbed into `20 · latticeW gradAlpha gradK`
(`gv_L_eq`, `gv_exp_le`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `t`-derivative prefactor of `hsE` (product rule, `a = 1 + ν t`). -/
def vsEd (ν t : ℝ) (j : ℤ) (x : ℝ × ℝ) : ℝ :=
  ν * (Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν t))
    * (-2 * (ageA ν t ^ 3)⁻¹ + sq2 (xj ν j x) * (ageA ν t ^ 4)⁻¹ / 4))

/-- The numerator `-(2 x_j · e_a)` of `hsL`. -/
def vsN (ν : ℝ) (j : ℤ) (x : ℝ × ℝ) (a : Fin 2) : ℝ :=
  -(2 * (xj ν j x).1 * (ei a).1 + 2 * (xj ν j x).2 * (ei a).2)

/-- `t`-derivative of `hsL` (quotient rule, as produced by `HasDerivAt.div`). -/
def vsLd (ν t : ℝ) (j : ℤ) (x : ℝ × ℝ) (a : Fin 2) : ℝ :=
  (0 * (4 * ageA ν t) - vsN ν j x a * (4 * ν)) / (4 * ageA ν t) ^ 2

lemma vs_A_hasDeriv (ν t : ℝ) : HasDerivAt (fun u => ageA ν u) ν t := by
  have h : HasDerivAt (fun u => 1 + ν * u) ν t := by
    simpa using ((hasDerivAt_id t).const_mul ν).const_add 1
  exact h

lemma vs_A_ge {ν t : ℝ} (hν : 0 ≤ ν) (ht : 0 ≤ t) : 1 ≤ ageA ν t := by
  unfold ageA
  linarith [mul_nonneg hν ht]

lemma vs_hsE_hasDeriv (ν : ℝ) (j : ℤ) (x : ℝ × ℝ) (t : ℝ) (hA : 1 ≤ ageA ν t) :
    HasDerivAt (fun u => hsE ν u j x) (vsEd ν t j x) t := by
  have hpos : 0 < ageA ν t := by linarith
  have hA0 : ageA ν t ≠ 0 := hpos.ne'
  have hA2 : HasDerivAt (fun u => ageA ν u ^ 2) (((2:ℕ):ℝ) * ageA ν t ^ (2 - 1) * ν) t :=
    (vs_A_hasDeriv ν t).pow 2
  have hI : HasDerivAt (fun u => (ageA ν u ^ 2)⁻¹)
      (-(((2:ℕ):ℝ) * ageA ν t ^ (2 - 1) * ν) / (ageA ν t ^ 2) ^ 2) t :=
    hA2.inv (pow_ne_zero 2 hA0)
  have hD : HasDerivAt (fun u => 4 * ageA ν u) (4 * ν) t := (vs_A_hasDeriv ν t).const_mul 4
  have hq : HasDerivAt (fun u => -(sq2 (xj ν j x)) / (4 * ageA ν u))
      ((0 * (4 * ageA ν t) - -(sq2 (xj ν j x)) * (4 * ν)) / (4 * ageA ν t) ^ 2) t :=
    (hasDerivAt_const t (-(sq2 (xj ν j x)))).div hD (mul_ne_zero (by norm_num) hA0)
  have hexp : HasDerivAt (fun u => Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν u)))
      (Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν t)) *
        ((0 * (4 * ageA ν t) - -(sq2 (xj ν j x)) * (4 * ν)) / (4 * ageA ν t) ^ 2)) t :=
    hq.exp
  have hprod : HasDerivAt (fun u => (ageA ν u ^ 2)⁻¹ * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν u)))
      ((-(((2:ℕ):ℝ) * ageA ν t ^ (2 - 1) * ν) / (ageA ν t ^ 2) ^ 2)
          * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν t))
        + (ageA ν t ^ 2)⁻¹ * (Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν t))
          * ((0 * (4 * ageA ν t) - -(sq2 (xj ν j x)) * (4 * ν)) / (4 * ageA ν t) ^ 2))) t :=
    hI.mul hexp
  unfold vsEd hsE
  convert hprod using 1
  field_simp
  ring

lemma vs_Vj_hasDeriv (ν : ℝ) (j : ℤ) (x : ℝ × ℝ) (t : ℝ) (hA : 1 ≤ ageA ν t) :
    HasDerivAt (fun u => Vj ν u j x) (vsEd ν t j x • Jrot (xj ν j x)) t :=
  (vs_hsE_hasDeriv ν j x t hA).smul_const (Jrot (xj ν j x))

lemma vs_deriv_Vj (ν : ℝ) (j : ℤ) (x : ℝ × ℝ) (s : ℝ) (hA : 1 ≤ ageA ν s) :
    deriv (fun t => Vj ν t j x) s = vsEd ν s j x • Jrot (xj ν j x) :=
  (vs_Vj_hasDeriv ν j x s hA).deriv

lemma vs_fderiv_eq (ν : ℝ) (j : ℤ) (x : ℝ × ℝ) (a : Fin 2) :
    (fun u => fderiv ℝ (Vj ν u j) x (ei a)) = fun u => hsG ν u j a x :=
  funext fun u => hs_eq ν u j a x

lemma vs_hsL_hasDeriv (ν : ℝ) (j : ℤ) (x : ℝ × ℝ) (a : Fin 2) (t : ℝ) (hA : 1 ≤ ageA ν t) :
    HasDerivAt (fun u => hsL ν u j a x) (vsLd ν t j x a) t := by
  have hpos : 0 < ageA ν t := by linarith
  have hD := (vs_A_hasDeriv ν t).const_mul 4
  have hq := (hasDerivAt_const t (vsN ν j x a)).div hD (mul_pos (by norm_num) hpos).ne'
  exact hq

lemma vs_hsG_hasDeriv (ν : ℝ) (j : ℤ) (x : ℝ × ℝ) (a : Fin 2) (t : ℝ) (hA : 1 ≤ ageA ν t) :
    HasDerivAt (fun u => hsG ν u j a x)
      (vsEd ν t j x • Jrot (ei a)
        + ((vsEd ν t j x * hsL ν t j a x + hsE ν t j x * vsLd ν t j x a) • Jrot (xj ν j x))) t := by
  have h1 := (vs_hsE_hasDeriv ν j x t hA).smul_const (Jrot (ei a))
  have h2 := ((vs_hsE_hasDeriv ν j x t hA).mul (vs_hsL_hasDeriv ν j x a t hA)).smul_const
    (Jrot (xj ν j x))
  exact h1.add h2

/-- `|(q)|` bound for the bracket of `vsEd`. -/
lemma vs_qr (A S : ℝ) (hA : 1 ≤ A) (hS : 0 ≤ S) :
    |-2 * (A ^ 3)⁻¹ + S * (A ^ 4)⁻¹ / 4| ≤ 2 + S / 4 := by
  have hq0 : 0 ≤ (A ^ 3)⁻¹ := inv_nonneg.2 (pow_nonneg (by linarith) 3)
  have hq1 : (A ^ 3)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hA)
  have hr0 : 0 ≤ (A ^ 4)⁻¹ := inv_nonneg.2 (pow_nonneg (by linarith) 4)
  have hr1 : (A ^ 4)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hA)
  have hSr0 : 0 ≤ S * (A ^ 4)⁻¹ := mul_nonneg hS hr0
  have hSr1 : S * (A ^ 4)⁻¹ ≤ S := mul_le_of_le_one_right hS hr1
  rw [abs_le]
  constructor <;> linarith

lemma vs_Ed_bound (ν s : ℝ) (j : ℤ) (x : ℝ × ℝ) (hν : 0 ≤ ν) (hA : 1 ≤ ageA ν s)
    (hS : 0 ≤ sq2 (xj ν j x)) :
    |vsEd ν s j x| ≤ ν * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) * (2 + sq2 (xj ν j x) / 4) := by
  unfold vsEd
  have hE0 : 0 ≤ Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) := (Real.exp_pos _).le
  have hq := vs_qr (ageA ν s) (sq2 (xj ν j x)) hA hS
  calc |ν * (Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s))
        * (-2 * (ageA ν s ^ 3)⁻¹ + sq2 (xj ν j x) * (ageA ν s ^ 4)⁻¹ / 4))|
      = ν * (Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s))
          * |-2 * (ageA ν s ^ 3)⁻¹ + sq2 (xj ν j x) * (ageA ν s ^ 4)⁻¹ / 4|) := by
        rw [abs_mul, abs_mul, abs_of_nonneg hν, abs_of_nonneg hE0]
    _ ≤ ν * (Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) * (2 + sq2 (xj ν j x) / 4)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hq hE0) hν
    _ = ν * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) * (2 + sq2 (xj ν j x) / 4) := by ring

lemma vs_hsE_le (ν s : ℝ) (j : ℤ) (x : ℝ × ℝ) (hA : 1 ≤ ageA ν s) :
    |hsE ν s j x| ≤ Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) := by
  unfold hsE
  have hE0 : 0 ≤ Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) := (Real.exp_pos _).le
  rw [abs_of_nonneg (mul_nonneg (inv_nonneg.2 (pow_nonneg (by linarith) 2)) hE0)]
  exact mul_le_of_le_one_left hE0 (inv_le_one_of_one_le₀ (one_le_pow₀ hA))

lemma vs_ei_abs (a : Fin 2) : |(ei a).1| ≤ 1 ∧ |(ei a).2| ≤ 1 := by
  fin_cases a <;> simp [ei]

lemma vs_N_le (X1 X2 c1 c2 B : ℝ) (hc1 : |c1| ≤ 1) (hc2 : |c2| ≤ 1)
    (hX : |X1| + |X2| ≤ B) : |-(2 * X1 * c1 + 2 * X2 * c2)| ≤ 2 * B := by
  rw [abs_neg]
  have h1 : |2 * X1 * c1| ≤ 2 * |X1| := by
    rw [abs_mul, abs_mul, abs_two]
    exact mul_le_of_le_one_right (by positivity) hc1
  have h2 : |2 * X2 * c2| ≤ 2 * |X2| := by
    rw [abs_mul, abs_mul, abs_two]
    exact mul_le_of_le_one_right (by positivity) hc2
  calc |2 * X1 * c1 + 2 * X2 * c2| ≤ |2 * X1 * c1| + |2 * X2 * c2| := abs_add_le _ _
    _ ≤ 2 * |X1| + 2 * |X2| := add_le_add h1 h2
    _ ≤ 2 * B := by linarith

lemma vs_hsL_le (ν t : ℝ) (j : ℤ) (x : ℝ × ℝ) (a : Fin 2) (B : ℝ) (hB : 0 ≤ B)
    (hA : 1 ≤ ageA ν t) (hN : |vsN ν j x a| ≤ 2 * B) : |hsL ν t j a x| ≤ 2 * B := by
  show |vsN ν j x a / (4 * ageA ν t)| ≤ 2 * B
  have h4 : 0 < 4 * ageA ν t := by linarith
  rw [abs_div, abs_of_pos h4, div_le_iff₀ h4]
  have : 2 * B ≤ 2 * B * (4 * ageA ν t) := le_mul_of_one_le_right (by linarith) (by linarith)
  linarith

lemma vs_vsLd_le (ν t : ℝ) (j : ℤ) (x : ℝ × ℝ) (a : Fin 2) (B : ℝ) (hν : 0 ≤ ν) (hB : 0 ≤ B)
    (hA : 1 ≤ ageA ν t) (hN : |vsN ν j x a| ≤ 2 * B) : |vsLd ν t j x a| ≤ B * ν := by
  unfold vsLd
  have h4 : 0 < 4 * ageA ν t := by linarith
  have hsq : 16 ≤ (4 * ageA ν t) ^ 2 := by nlinarith
  rw [abs_div, abs_of_pos (pow_pos h4 2), div_le_iff₀ (pow_pos h4 2)]
  have hnum : |0 * (4 * ageA ν t) - vsN ν j x a * (4 * ν)| ≤ 8 * B * ν := by
    rw [zero_mul, zero_sub, abs_neg, abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ 4 * ν)]
    calc |vsN ν j x a| * (4 * ν) ≤ (2 * B) * (4 * ν) :=
          mul_le_mul_of_nonneg_right hN (by linarith)
      _ = 8 * B * ν := by ring
  have hBν : 0 ≤ B * ν := mul_nonneg hB hν
  have := mul_le_mul_of_nonneg_left hsq hBν
  linarith

lemma vs_kappa (ν Ed L P Ld E Q B : ℝ) (hEd : |Ed| ≤ Q) (hQ0 : 0 ≤ Q) (hL : |L| ≤ 2 * B)
    (hP : |P| ≤ E) (hLd : |Ld| ≤ B * ν) (hE : 0 ≤ E) :
    |Ed * L + P * Ld| ≤ Q * (2 * B) + E * (B * ν) := by
  calc |Ed * L + P * Ld| ≤ |Ed * L| + |P * Ld| := abs_add_le _ _
    _ = |Ed| * |L| + |P| * |Ld| := by rw [abs_mul, abs_mul]
    _ ≤ Q * (2 * B) + E * (B * ν) :=
        add_le_add (mul_le_mul hEd hL (abs_nonneg _) hQ0) (mul_le_mul hP hLd (abs_nonneg _) hE)

lemma vs_norm2 (c1 c2 : ℝ) (w1 w2 : ℝ × ℝ) :
    ‖c1 • Jrot w1 + c2 • Jrot w2‖ ≤ |c1| * ‖w1‖ + |c2| * ‖w2‖ := by
  calc ‖c1 • Jrot w1 + c2 • Jrot w2‖ ≤ ‖c1 • Jrot w1‖ + ‖c2 • Jrot w2‖ := norm_add_le _ _
    _ = |c1| * ‖w1‖ + |c2| * ‖w2‖ := by rw [hs_smul_jrot, hs_smul_jrot]

lemma vs_poly1 (B S : ℝ) (hB : 1 ≤ B) (hS : 0 ≤ S) (hSB : S ≤ B ^ 2) :
    B * ((2 + S / 4) * (1 + S)) ≤ 6 * B ^ 5 := by
  have hB0 : 0 ≤ B := by linarith
  have hB2 : 1 ≤ B ^ 2 := one_le_pow₀ hB
  have h1 : 2 + S / 4 ≤ 3 * B ^ 2 := by linarith
  have h3 : 1 + S ≤ 2 * B ^ 2 := by linarith
  have h4 : (2 + S / 4) * (1 + S) ≤ (3 * B ^ 2) * (2 * B ^ 2) :=
    mul_le_mul h1 h3 (by linarith) (by positivity)
  calc B * ((2 + S / 4) * (1 + S)) ≤ B * ((3 * B ^ 2) * (2 * B ^ 2)) :=
        mul_le_mul_of_nonneg_left h4 hB0
    _ = 6 * B ^ 5 := by ring

lemma vs_poly2 (B S : ℝ) (hB : 1 ≤ B) (hS : 0 ≤ S) (hSB : S ≤ B ^ 2) :
    B * ((2 + S / 4) + B * (5 + S / 2) * (1 + S)) ≤ 15 * B ^ 6 := by
  have hB0 : 0 ≤ B := by linarith
  have hB2 : 1 ≤ B ^ 2 := one_le_pow₀ hB
  have h1 : 2 + S / 4 ≤ 3 * B ^ 2 := by linarith
  have h5 : 5 + S / 2 ≤ 6 * B ^ 2 := by linarith
  have h3 : 1 + S ≤ 2 * B ^ 2 := by linarith
  have h4 : (5 + S / 2) * (1 + S) ≤ (6 * B ^ 2) * (2 * B ^ 2) :=
    mul_le_mul h5 h3 (by linarith) (by positivity)
  have e1 : B * ((2 + S / 4) + B * (5 + S / 2) * (1 + S))
      = B * (2 + S / 4) + B ^ 2 * ((5 + S / 2) * (1 + S)) := by ring
  have f1 : B * (2 + S / 4) ≤ 3 * B ^ 3 := by
    calc B * (2 + S / 4) ≤ B * (3 * B ^ 2) := mul_le_mul_of_nonneg_left h1 hB0
      _ = 3 * B ^ 3 := by ring
  have f2 : B ^ 2 * ((5 + S / 2) * (1 + S)) ≤ B ^ 2 * (12 * B ^ 4) := by
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg B)
    calc (5 + S / 2) * (1 + S) ≤ (6 * B ^ 2) * (2 * B ^ 2) := h4
      _ = 12 * B ^ 4 := by ring
  have f3 : B ^ 3 ≤ B ^ 6 := pow_le_pow_right₀ hB (by norm_num)
  have f4 : B ^ 2 * (12 * B ^ 4) = 12 * B ^ 6 := by ring
  rw [e1]
  linarith [f1, f2, f3, f4]

lemma vs_bound3 (B S E T ν s : ℝ) (hB : 1 ≤ B) (hS : 0 ≤ S) (hSB : S ≤ B ^ 2) (hE : 0 ≤ E)
    (hET : E ≤ T) (hν : 0 ≤ ν) (hs : 0 ≤ s) (hνs : ν * s ≤ 11 / 10) :
    B * (s * (ν * E * (2 + S / 4) * (1 + S))) ≤ 20 * (B ^ 12 * T) := by
  have hB0 : 0 ≤ B := by linarith
  have hT : 0 ≤ T := le_trans hE hET
  have p := vs_poly1 B S hB hS hSB
  have hB5 : B ^ 5 ≤ B ^ 12 := pow_le_pow_right₀ hB (by norm_num)
  have hEB : E * B ^ 5 ≤ T * B ^ 12 := mul_le_mul hET hB5 (by positivity) hT
  have hX : 0 ≤ (2 + S / 4) * (1 + S) := mul_nonneg (by linarith) (by linarith)
  calc B * (s * (ν * E * (2 + S / 4) * (1 + S)))
      = (ν * s) * (E * (B * ((2 + S / 4) * (1 + S)))) := by ring
    _ ≤ (11 / 10) * (E * (6 * B ^ 5)) :=
        mul_le_mul hνs (mul_le_mul_of_nonneg_left p hE) (mul_nonneg hE (mul_nonneg hB0 hX))
          (by norm_num)
    _ = (11 / 10) * 6 * (E * B ^ 5) := by ring
    _ ≤ (11 / 10) * 6 * (T * B ^ 12) := mul_le_mul_of_nonneg_left hEB (by norm_num)
    _ ≤ 20 * (B ^ 12 * T) := by nlinarith [mul_nonneg (pow_nonneg hB0 12) hT]

lemma vs_bound4 (B S E T ν s : ℝ) (hB : 1 ≤ B) (hS : 0 ≤ S) (hSB : S ≤ B ^ 2) (hE : 0 ≤ E)
    (hET : E ≤ T) (hν : 0 ≤ ν) (hs : 0 ≤ s) (hνs : ν * s ≤ 11 / 10) :
    B * (s * (ν * E * ((2 + S / 4) + B * (5 + S / 2) * (1 + S)))) ≤ 20 * (B ^ 12 * T) := by
  have hB0 : 0 ≤ B := by linarith
  have hT : 0 ≤ T := le_trans hE hET
  have p := vs_poly2 B S hB hS hSB
  have hB6 : B ^ 6 ≤ B ^ 12 := pow_le_pow_right₀ hB (by norm_num)
  have hEB : E * B ^ 6 ≤ T * B ^ 12 := mul_le_mul hET hB6 (by positivity) hT
  have hK0 : 0 ≤ (2 + S / 4) + B * (5 + S / 2) * (1 + S) := by
    have := mul_nonneg (mul_nonneg hB0 (by linarith : (0:ℝ) ≤ 5 + S / 2))
      (by linarith : (0:ℝ) ≤ 1 + S)
    linarith
  calc B * (s * (ν * E * ((2 + S / 4) + B * (5 + S / 2) * (1 + S))))
      = (ν * s) * (E * (B * ((2 + S / 4) + B * (5 + S / 2) * (1 + S)))) := by ring
    _ ≤ (11 / 10) * (E * (15 * B ^ 6)) :=
        mul_le_mul hνs (mul_le_mul_of_nonneg_left p hE)
          (mul_nonneg hE (mul_nonneg hB0 hK0)) (by norm_num)
    _ = (11 / 10) * 15 * (E * B ^ 6) := by ring
    _ ≤ (11 / 10) * 15 * (T * B ^ 12) := mul_le_mul_of_nonneg_left hEB (by norm_num)
    _ ≤ 20 * (B ^ 12 * T) := by nlinarith [mul_nonneg (pow_nonneg hB0 12) hT]

theorem gradVjSBounds : ∃ C : ℝ, 0 ≤ C ∧ ∀ (ν s : ℝ) (j : ℤ) (x : ℝ × ℝ), 0 < ν → ν ≤ 1 → 0 < s → s ≤ (11 / 10) / ν → ∀ a : Fin 2, (∀ s' : ℝ, 0 < s' → DifferentiableAt ℝ (fun t => Vj ν t j x) s') ∧ (∀ s' : ℝ, 0 < s' → DifferentiableAt ℝ (fun t => fderiv ℝ (Vj ν t j) x (ei a)) s') ∧ (1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|) * (s * ‖deriv (fun t => Vj ν t j x) s‖) ≤ C * gradW ν x j ∧ (1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|) * (s * ‖deriv (fun t => fderiv ℝ (Vj ν t j) x (ei a)) s‖) ≤ C * gradW ν x j := by
  refine ⟨20, by norm_num, ?_⟩
  intro ν s j x hν hν1 hs hs1 a
  have hνs : ν * s ≤ 11 / 10 := by
    have h := (le_div_iff₀ hν).mp hs1
    linarith [mul_comm s ν]
  have hν0 : 0 ≤ ν := hν.le
  have hs0 : 0 ≤ s := hs.le
  have hA : 1 ≤ ageA ν s := vs_A_ge hν0 hs0
  have hA2 : ageA ν s ≤ 21 / 10 := by unfold ageA; linarith
  have hA' : ∀ s' : ℝ, 0 < s' → 1 ≤ ageA ν s' := fun s' hs' => vs_A_ge hν0 hs'.le
  have hS0 : 0 ≤ sq2 (xj ν j x) := hu_sq2_nonneg _
  have hSB : sq2 (xj ν j x) ≤ (1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|) ^ 2 :=
    gv_sq_le (x.1 - (j : ℝ) * cOf ν) x.2
  have hB1 : (1 : ℝ) ≤ 1 + |x.1 - (j : ℝ) * cOf ν| + |x.2| := by
    linarith [abs_nonneg (x.1 - (j : ℝ) * cOf ν), abs_nonneg x.2]
  have hBX : |(xj ν j x).1| + |(xj ν j x).2| ≤ 1 + |x.1 - (j : ℝ) * cOf ν| + |x.2| := by
    show |x.1 - (j : ℝ) * cOf ν| + |x.2| ≤ _
    linarith
  have hWeq : gradW ν x j = (1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|) ^ 12
      * Real.exp (-(1 / 9) * sq2 (xj ν j x)) :=
    gv_L_eq (x.1 - (j : ℝ) * cOf ν) x.2
  have hET : Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) ≤ Real.exp (-(1 / 9) * sq2 (xj ν j x)) :=
    gv_exp_le _ _ hS0 hA hA2
  have hE0 : 0 ≤ Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) := (Real.exp_pos _).le
  have hB0 : (0 : ℝ) ≤ 1 + |x.1 - (j : ℝ) * cOf ν| + |x.2| := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s' hs'
    exact (vs_Vj_hasDeriv ν j x s' (hA' s' hs')).differentiableAt
  · intro s' hs'
    rw [vs_fderiv_eq]
    exact (vs_hsG_hasDeriv ν j x a s' (hA' s' hs')).differentiableAt
  · rw [vs_deriv_Vj ν j x s hA, hs_smul_jrot, hWeq]
    have hd := vs_Ed_bound ν s j x hν0 hA hS0
    have hn := gv_norm_le (xj ν j x)
    calc (1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|) * (s * (|vsEd ν s j x| * ‖xj ν j x‖))
        ≤ (1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|) *
            (s * (ν * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) * (2 + sq2 (xj ν j x) / 4)
              * (1 + sq2 (xj ν j x)))) := by
          apply mul_le_mul_of_nonneg_left _ hB0
          apply mul_le_mul_of_nonneg_left _ hs0
          exact mul_le_mul hd hn (norm_nonneg _)
            (mul_nonneg (mul_nonneg hν0 hE0) (by linarith))
      _ ≤ 20 * ((1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|) ^ 12
            * Real.exp (-(1 / 9) * sq2 (xj ν j x))) :=
          vs_bound3 _ _ _ _ _ _ hB1 hS0 hSB hE0 hET hν0 hs0 hνs
  · rw [vs_fderiv_eq, (vs_hsG_hasDeriv ν j x a s hA).deriv, hWeq]
    have hd := vs_Ed_bound ν s j x hν0 hA hS0
    have hN : |vsN ν j x a| ≤ 2 * (1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|) := by
      obtain ⟨c1, c2⟩ := vs_ei_abs a
      exact vs_N_le _ _ _ _ _ c1 c2 hBX
    have hL := vs_hsL_le ν s j x a _ hB0 hA hN
    have hLd := vs_vsLd_le ν s j x a _ hν0 hB0 hA hN
    have hP := vs_hsE_le ν s j x hA
    have hk := vs_kappa _ _ _ _ _ _ _ _ hd (mul_nonneg (mul_nonneg hν0 hE0) (by linarith))
      hL hP hLd hE0
    have hn := gv_norm_le (xj ν j x)
    have hei := hs_ei_norm_le a
    have hGn := vs_norm2 (vsEd ν s j x) (vsEd ν s j x * hsL ν s j a x + hsE ν s j x * vsLd ν s j x a)
      (ei a) (xj ν j x)
    have hG : ‖vsEd ν s j x • Jrot (ei a)
        + ((vsEd ν s j x * hsL ν s j a x + hsE ν s j x * vsLd ν s j x a) • Jrot (xj ν j x))‖
        ≤ ν * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s))
            * ((2 + sq2 (xj ν j x) / 4) + (1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|)
              * (5 + sq2 (xj ν j x) / 2) * (1 + sq2 (xj ν j x))) := by
      refine hGn.trans ?_
      have hq1 : |vsEd ν s j x| * ‖ei a‖ ≤ |vsEd ν s j x| :=
        mul_le_of_le_one_right (abs_nonneg _) hei
      have hQ : 0 ≤ ν * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) * (2 + sq2 (xj ν j x) / 4) :=
        mul_nonneg (mul_nonneg hν0 hE0) (by linarith)
      have hQ' : 0 ≤ ν * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) * (2 + sq2 (xj ν j x) / 4) :=
        mul_nonneg (mul_nonneg hν0 hE0) (by linarith)
      have hq2 : |vsEd ν s j x * hsL ν s j a x + hsE ν s j x * vsLd ν s j x a| * ‖xj ν j x‖
          ≤ (ν * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) * (2 + sq2 (xj ν j x) / 4) * (2 * (1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|)) + Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) * ((1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|) * ν)) * (1 + sq2 (xj ν j x)) :=
        mul_le_mul hk hn (norm_nonneg _)
          (add_nonneg (mul_nonneg hQ' (by linarith)) (mul_nonneg hE0 (mul_nonneg hB0 hν0)))
      calc _ ≤ ν * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) * (2 + sq2 (xj ν j x) / 4) + (ν * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) * (2 + sq2 (xj ν j x) / 4) * (2 * (1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|)) + Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) * ((1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|) * ν)) * (1 + sq2 (xj ν j x)) :=
            add_le_add (hq1.trans hd) hq2
        _ = ν * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) * ((2 + sq2 (xj ν j x) / 4) + (1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|) * (5 + sq2 (xj ν j x) / 2) * (1 + sq2 (xj ν j x))) := by ring
    calc (1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|) * (s * ‖vsEd ν s j x • Jrot (ei a)
          + ((vsEd ν s j x * hsL ν s j a x + hsE ν s j x * vsLd ν s j x a) • Jrot (xj ν j x))‖)
        ≤ (1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|) * (s * (ν * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s))
            * ((2 + sq2 (xj ν j x) / 4) + (1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|)
              * (5 + sq2 (xj ν j x) / 2) * (1 + sq2 (xj ν j x))))) := by
          apply mul_le_mul_of_nonneg_left _ hB0
          exact mul_le_mul_of_nonneg_left hG hs0
      _ ≤ 20 * ((1 + |x.1 - (j : ℝ) * cOf ν| + |x.2|) ^ 12
            * Real.exp (-(1 / 9) * sq2 (xj ν j x))) :=
          vs_bound4 _ _ _ _ _ _ hB1 hS0 hSB hE0 hET hν0 hs0 hνs

end UnforcedLeray.Short.PartIIIb.Concrete
