import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_8.Cross.BrkDeriv

/-!
# `PartIII-b:C/asrc/ra/8/2/org` : the pair bound (spec item (a))

Source `the November 2 reference manuscript`
5026-5031: `P_{jk} = Db_j V_k + DV_k b_j` is a polynomial in `x_j, x_k` times
`e^{-(|x_j|²+|x_k|²)/(4a)}`, linear in `|B|`: from `rcBrkPointwise`, `rcBrkDerivPointwise`,
`|V_k| ≤ e_k|x_k|` and `|DV_k w| ≤ e_k(1+|x_k|²)|w|`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem rcPairPointwise : RcPairPointwise := by
  obtain ⟨C1, hC1, hB1⟩ := rcBrkPointwise
  obtain ⟨C2, hC2, hB2⟩ := rcBrkDerivPointwise
  refine ⟨C1 + C2, by positivity, ?_⟩
  intro ν s B j k x hν hν1 hs hsT
  have ha1 : 1 ≤ ageA ν s := by unfold ageA; nlinarith [mul_pos hν hs]
  have ha0 : 0 < ageA ν s := by linarith
  set a := ageA ν s with hadef
  set Ej := Real.exp (-(sq2 (xj ν j x)) / (4 * a)) with hEj
  set Ek := Real.exp (-(sq2 (xj ν k x)) / (4 * a)) with hEk
  set Sj := sq2 (xj ν j x) with hSj
  set Sk := sq2 (xj ν k x) with hSk
  set F := frob B with hFdef
  have hEj0 : 0 ≤ Ej := (Real.exp_pos _).le
  have hEk0 : 0 ≤ Ek := (Real.exp_pos _).le
  have hF0 : 0 ≤ F := Real.sqrt_nonneg _
  have hrk : ‖xj ν k x‖ ^ 2 ≤ Sk := hu_norm_sq_le _
  have hSk0 : 0 ≤ Sk := le_trans (sq_nonneg _) hrk
  have hrj : ‖xj ν j x‖ ^ 2 ≤ Sj := hu_norm_sq_le _
  have hSj0 : 0 ≤ Sj := le_trans (sq_nonneg _) hrj
  have hrk1 : ‖xj ν k x‖ ≤ 1 + Sk := by nlinarith [sq_nonneg (‖xj ν k x‖ - 1), norm_nonneg (xj ν k x)]
  have hκ0 : 0 ≤ (a ^ 2)⁻¹ := by positivity
  have hκ : (a ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith)
  -- |V_k| ≤ e_k (1 + |x_k|²)
  have hVk : ‖Vj ν s k x‖ ≤ Ek * (1 + Sk) := by
    rw [gp_Vj_norm_eq]
    have h1 : (a ^ 2)⁻¹ * Ek ≤ Ek := by
      have := mul_le_mul_of_nonneg_right hκ hEk0
      linarith
    exact mul_le_mul h1 hrk1 (norm_nonneg _) hEk0
  have t1 : ‖fderiv ℝ (rcBrk ν s B j) x (Vj ν s k x)‖ ≤
      C2 * F * (1 + Sj) ^ 3 * Ej * (Ek * (1 + Sk)) :=
    (hB2 ν s B j x _ hν hν1 hs hsT).trans
      (mul_le_mul_of_nonneg_left hVk (by positivity))
  have t2 : ‖fderiv ℝ (Vj ν s k) x (rcBrk ν s B j x)‖ ≤
      Ek * (1 + Sk) * (C1 * F * (1 + Sj) ^ 2 * Ej) :=
    (rc_fderiv_Vj_le ν s ha1 k x _).trans
      (mul_le_mul_of_nonneg_left (hB1 ν s B j x hν hν1 hs hsT) (by positivity))
  have hexp : Real.exp (-(Sj + Sk) / (4 * a)) = Ej * Ek := by
    rw [hEj, hEk, ← Real.exp_add]
    congr 1
    ring
  rw [hexp]
  unfold rcPair
  refine (norm_add_le _ _).trans ((add_le_add t1 t2).trans ?_)
  have hPj : 1 ≤ 1 + Sj := by linarith
  have hPk : 1 ≤ 1 + Sk := by linarith
  have hPj2 : (1 + Sj) ^ 2 ≤ (1 + Sj) ^ 3 := pow_le_pow_right₀ hPj (by norm_num)
  have hPk3 : 1 + Sk ≤ (1 + Sk) ^ 3 := by
    calc 1 + Sk = (1 + Sk) ^ 1 := (pow_one _).symm
      _ ≤ (1 + Sk) ^ 3 := pow_le_pow_right₀ hPk (by norm_num)
  have hX : 0 ≤ F * Ej * Ek := by positivity
  have hY : (1 + Sj) ^ 2 * (1 + Sk) ≤ (1 + Sj) ^ 3 * (1 + Sk) ^ 3 :=
    mul_le_mul hPj2 hPk3 (by positivity) (by positivity)
  have hZ : (1 + Sj) ^ 3 * (1 + Sk) ≤ (1 + Sj) ^ 3 * (1 + Sk) ^ 3 :=
    mul_le_mul_of_nonneg_left hPk3 (by positivity)
  have e1 : C2 * F * (1 + Sj) ^ 3 * Ej * (Ek * (1 + Sk)) =
      C2 * (F * Ej * Ek) * ((1 + Sj) ^ 3 * (1 + Sk)) := by ring
  have e2 : Ek * (1 + Sk) * (C1 * F * (1 + Sj) ^ 2 * Ej) =
      C1 * (F * Ej * Ek) * ((1 + Sj) ^ 2 * (1 + Sk)) := by ring
  have e3 : (C1 + C2) * F * ((1 + Sj) ^ 3 * (1 + Sk) ^ 3) * (Ej * Ek) =
      C1 * (F * Ej * Ek) * ((1 + Sj) ^ 3 * (1 + Sk) ^ 3) +
        C2 * (F * Ej * Ek) * ((1 + Sj) ^ 3 * (1 + Sk) ^ 3) := by ring
  rw [e1, e2, e3]
  have f1 := mul_le_mul_of_nonneg_left hZ (mul_nonneg hC2 hX)
  have f2 := mul_le_mul_of_nonneg_left hY (mul_nonneg hC1 hX)
  linarith

end UnforcedLeray.Short.PartIIIb.Concrete
