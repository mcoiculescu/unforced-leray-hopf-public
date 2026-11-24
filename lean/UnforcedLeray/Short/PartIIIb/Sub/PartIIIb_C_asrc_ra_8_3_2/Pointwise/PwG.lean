import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_8_3_2.Pointwise.Value

set_option autoImplicit false

noncomputable section

open Set Real

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The explicit first derivative of `V_j` in a fixed direction `u` (as a function of the point). -/
def pwG (ν s : ℝ) (j : ℤ) (u : ℝ × ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  ((ageA ν s ^ 2)⁻¹ * Real.exp (-(sq2 (xj ν j z)) / (4 * ageA ν s))) • Jrot u
    + ((ageA ν s ^ 2)⁻¹ * (Real.exp (-(sq2 (xj ν j z)) / (4 * ageA ν s)) *
        (-(2 * (xj ν j z).1 * u.1 + 2 * (xj ν j z).2 * u.2) / (4 * ageA ν s)))) • Jrot (xj ν j z)

lemma pw_fderiv_Vj_eq (ν s : ℝ) (j : ℤ) (z u : ℝ × ℝ) :
    fderiv ℝ (Vj ν s j) z u = pwG ν s j u z :=
  gp_fderiv_Vj ν s j z u

/-- Abstract algebra for the second-derivative bound. -/
lemma pw_alg_D (κ E n nv nu p q r : ℝ) (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) (hE : 0 ≤ E) (hn : 0 ≤ n)
    (hnv : 0 ≤ nv) (hnu : 0 ≤ nu) (hp : p ≤ n * nv) (hq : q ≤ n * nu) (hr : r ≤ nv * nu)
    (hp0 : 0 ≤ p) (hq0 : 0 ≤ q) (hr0 : 0 ≤ r) :
    κ * E * p * nu + κ * E * (p * q + r) * n + κ * E * q * nv ≤ 4 * E * (1 + n) ^ 3 * nv * nu := by
  have hκE : κ * E ≤ E := mul_le_of_le_one_left hE hκ1
  have hκE0 : 0 ≤ κ * E := mul_nonneg hκ0 hE
  have h1 : p * nu ≤ n * nv * nu := mul_le_mul_of_nonneg_right hp hnu
  have h2 : p * q ≤ (n * nv) * (n * nu) := mul_le_mul hp hq hq0 (mul_nonneg hn hnv)
  have h3 : (p * q + r) * n ≤ ((n * nv) * (n * nu) + nv * nu) * n :=
    mul_le_mul_of_nonneg_right (add_le_add h2 hr) hn
  have h4 : q * nv ≤ n * nu * nv := mul_le_mul_of_nonneg_right hq hnv
  have hX : p * nu + (p * q + r) * n + q * nv ≤ nv * nu * (3 * n + n ^ 3) := by
    nlinarith [h1, h3, h4]
  have hX0 : 0 ≤ nv * nu * (3 * n + n ^ 3) := by
    have : 0 ≤ 3 * n + n ^ 3 := by nlinarith [pow_nonneg hn 3]
    exact mul_nonneg (mul_nonneg hnv hnu) this
  have hY : 3 * n + n ^ 3 ≤ 4 * (1 + n) ^ 3 := by
    nlinarith [pow_nonneg hn 2, pow_nonneg hn 3]
  calc κ * E * p * nu + κ * E * (p * q + r) * n + κ * E * q * nv
      = κ * E * (p * nu + (p * q + r) * n + q * nv) := by ring
    _ ≤ E * (p * nu + (p * q + r) * n + q * nv) := by
        apply mul_le_mul_of_nonneg_right hκE
        have e1 := mul_nonneg hp0 hnu
        have e2 := mul_nonneg (add_nonneg (mul_nonneg hp0 hq0) hr0) hn
        have e3 := mul_nonneg hq0 hnv
        linarith
    _ ≤ E * (nv * nu * (3 * n + n ^ 3)) := mul_le_mul_of_nonneg_left hX hE
    _ ≤ E * (nv * nu * (4 * (1 + n) ^ 3)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hY (mul_nonneg hnv hnu)) hE
    _ = 4 * E * (1 + n) ^ 3 * nv * nu := by ring


/-- Abstract form of the absolute-value bound for the three terms of the line derivative. -/
lemma pw_alg_abs (κ E n nv nu Lxv Lxu Lvu : ℝ) (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) (hE : 0 ≤ E)
    (hn : 0 ≤ n) (hnv : 0 ≤ nv) (hnu : 0 ≤ nu) (hp : |Lxv| ≤ n * nv) (hq : |Lxu| ≤ n * nu)
    (hr : |Lvu| ≤ nv * nu) :
    |κ * (E * Lxv)| * nu + (|κ * ((E * Lxv) * Lxu + E * Lvu)| * n + |κ * (E * Lxu)| * nv)
      ≤ 4 * E * (1 + n) ^ 3 * nv * nu := by
  have e1 : |κ * (E * Lxv)| = κ * E * |Lxv| := by
    rw [abs_mul, abs_mul, abs_of_nonneg hκ0, abs_of_nonneg hE]; ring
  have e3 : |κ * (E * Lxu)| = κ * E * |Lxu| := by
    rw [abs_mul, abs_mul, abs_of_nonneg hκ0, abs_of_nonneg hE]; ring
  have hsum : |(E * Lxv) * Lxu + E * Lvu| ≤ E * (|Lxv| * |Lxu| + |Lvu|) := by
    calc |(E * Lxv) * Lxu + E * Lvu| ≤ |(E * Lxv) * Lxu| + |E * Lvu| := abs_add_le _ _
      _ = E * (|Lxv| * |Lxu|) + E * |Lvu| := by
          rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hE]; ring
      _ = E * (|Lxv| * |Lxu| + |Lvu|) := by ring
  have e2 : |κ * ((E * Lxv) * Lxu + E * Lvu)| ≤ κ * E * (|Lxv| * |Lxu| + |Lvu|) := by
    rw [abs_mul, abs_of_nonneg hκ0]
    calc κ * |(E * Lxv) * Lxu + E * Lvu| ≤ κ * (E * (|Lxv| * |Lxu| + |Lvu|)) :=
          mul_le_mul_of_nonneg_left hsum hκ0
      _ = κ * E * (|Lxv| * |Lxu| + |Lvu|) := by ring
  have hp0 := abs_nonneg Lxv
  have hq0 := abs_nonneg Lxu
  have hr0 := abs_nonneg Lvu
  rw [e1, e3]
  calc κ * E * |Lxv| * nu + (|κ * ((E * Lxv) * Lxu + E * Lvu)| * n + κ * E * |Lxu| * nv)
      ≤ κ * E * |Lxv| * nu + (κ * E * (|Lxv| * |Lxu| + |Lvu|) * n + κ * E * |Lxu| * nv) := by
        gcongr
    _ = κ * E * |Lxv| * nu + κ * E * (|Lxv| * |Lxu| + |Lvu|) * n + κ * E * |Lxu| * nv := by ring
    _ ≤ 4 * E * (1 + n) ^ 3 * nv * nu :=
        pw_alg_D κ E n nv nu |Lxv| |Lxu| |Lvu| hκ0 hκ1 hE hn hnv hnu hp hq hr hp0 hq0 hr0

/-- The base-point derivative of the line `t ↦ pwG u (x + t v)`. -/
def pwGD (ν s : ℝ) (j : ℤ) (x v u : ℝ × ℝ) : ℝ × ℝ :=
  ((ageA ν s ^ 2)⁻¹ * (Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) *
      (-(2 * (xj ν j x).1 * v.1 + 2 * (xj ν j x).2 * v.2) / (4 * ageA ν s)))) • Jrot u
    + (((ageA ν s ^ 2)⁻¹ * (Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) *
          (-(2 * (xj ν j x).1 * u.1 + 2 * (xj ν j x).2 * u.2) / (4 * ageA ν s)))) • Jrot v
      + ((ageA ν s ^ 2)⁻¹ * ((Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) *
          (-(2 * (xj ν j x).1 * v.1 + 2 * (xj ν j x).2 * v.2) / (4 * ageA ν s))) *
          (-(2 * (xj ν j x).1 * u.1 + 2 * (xj ν j x).2 * u.2) / (4 * ageA ν s))
          + Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) *
          (-(2 * v.1 * u.1 + 2 * v.2 * u.2) / (4 * ageA ν s)))) • Jrot (xj ν j x))

/-- The line derivative of `pwG` at the base point. -/
lemma pwG_line_hasDerivAt (ν s : ℝ) (j : ℤ) (x v u : ℝ × ℝ) :
    HasDerivAt (fun t : ℝ => pwG ν s j u (x + t • v)) (pwGD ν s j x v u) 0 := by
  have hx : HasDerivAt (fun t : ℝ => (xj ν j (x + t • v)).1) v.1 0 := by
    have : HasDerivAt (fun t : ℝ => x.1 + t * v.1 - (j : ℝ) * cOf ν) v.1 0 := by
      have h := (((hasDerivAt_id' (0:ℝ)).mul_const v.1).const_add x.1).sub_const ((j : ℝ) * cOf ν)
      simpa using h
    exact this
  have hy : HasDerivAt (fun t : ℝ => (xj ν j (x + t • v)).2) v.2 0 := by
    have : HasDerivAt (fun t : ℝ => x.2 + t * v.2) v.2 0 := by
      have h := ((hasDerivAt_id' (0:ℝ)).mul_const v.2).const_add x.2
      simpa using h
    exact this
  have hE := gp_exp_line ν s j x v
  have hL : HasDerivAt
      (fun t : ℝ => -(2 * (xj ν j (x + t • v)).1 * u.1 + 2 * (xj ν j (x + t • v)).2 * u.2) / (4 * ageA ν s))
      (-(2 * v.1 * u.1 + 2 * v.2 * u.2) / (4 * ageA ν s)) 0 := by
    have h := ((((hx.const_mul 2).mul_const u.1).add ((hy.const_mul 2).mul_const u.2)).neg).div_const
      (4 * ageA ν s)
    refine h.congr_deriv ?_
    ring
  have hP := hE.const_mul ((ageA ν s ^ 2)⁻¹)
  have hQ := (hE.mul hL).const_mul ((ageA ν s ^ 2)⁻¹)
  have hJ : HasDerivAt (fun t : ℝ => Jrot (xj ν j (x + t • v))) (Jrot v) 0 := by
    unfold Jrot
    exact (hy.neg).prodMk hx
  have hfull := (hP.smul_const (Jrot u)).add (hQ.smul hJ)
  unfold pwG pwGD
  refine hfull.congr_deriv ?_
  simp only [zero_smul, add_zero, Pi.mul_apply]

/-- Norm bound of the base-point line derivative. -/
lemma pwGD_norm_le (ν s : ℝ) (j : ℤ) (ha : 0 < ageA ν s) (hb : 1 ≤ ageA ν s) (x v u : ℝ × ℝ) :
    ‖pwGD ν s j x v u‖ ≤
      4 * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) * (1 + ‖xj ν j x‖) ^ 3 * ‖v‖ * ‖u‖ := by
  have hκ0 : 0 ≤ (ageA ν s ^ 2)⁻¹ := inv_nonneg.2 (sq_nonneg _)
  have hκ1 : (ageA ν s ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hb)
  have hE0 : 0 ≤ Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) := (Real.exp_pos _).le
  have hLxv : |-(2 * (xj ν j x).1 * v.1 + 2 * (xj ν j x).2 * v.2) / (4 * ageA ν s)|
      ≤ ‖xj ν j x‖ * ‖v‖ :=
    (gp_c1_abs (xj ν j x) v (ageA ν s) ha).trans (div_le_self (by positivity) hb)
  have hLxu : |-(2 * (xj ν j x).1 * u.1 + 2 * (xj ν j x).2 * u.2) / (4 * ageA ν s)|
      ≤ ‖xj ν j x‖ * ‖u‖ :=
    (gp_c1_abs (xj ν j x) u (ageA ν s) ha).trans (div_le_self (by positivity) hb)
  have hLvu : |-(2 * v.1 * u.1 + 2 * v.2 * u.2) / (4 * ageA ν s)| ≤ ‖v‖ * ‖u‖ :=
    (gp_c1_abs v u (ageA ν s) ha).trans (div_le_self (by positivity) hb)
  unfold pwGD
  refine (norm_add_le _ _).trans ((add_le_add le_rfl (norm_add_le _ _)).trans ?_)
  simp only [norm_smul, gp_jrot_norm, Real.norm_eq_abs]
  have key := pw_alg_abs (ageA ν s ^ 2)⁻¹ (Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)))
    ‖xj ν j x‖ ‖v‖ ‖u‖
    (-(2 * (xj ν j x).1 * v.1 + 2 * (xj ν j x).2 * v.2) / (4 * ageA ν s))
    (-(2 * (xj ν j x).1 * u.1 + 2 * (xj ν j x).2 * u.2) / (4 * ageA ν s))
    (-(2 * v.1 * u.1 + 2 * v.2 * u.2) / (4 * ageA ν s))
    hκ0 hκ1 hE0 (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hLxv hLxu hLvu
  linarith

end UnforcedLeray.Short.PartIIIb.Concrete
