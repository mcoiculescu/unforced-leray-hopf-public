import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_8.Cross.BrkFDeriv
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_8.Cross.HessDir
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_8.Cross.BrkPointwise

/-!
# `PartIII-b:C/asrc/ra/8/2/org` : pointwise bound of the derivative of `b_j`

Source `the November 2 reference manuscript`
4963-4972: `Db_j(x)v = B_mer(DV_j(x)v) - (DV_j(x)(B_mer v) + D²V_j(x)[v][B_mer x_j])`
(`rc_brk_fderiv`), with `|DV_j w| ≤ e(1+|x_j|²)|w|`, `|D²V_j[v][w]| ≤ K(1+|x_j|²)²e|v||w|`
(`rcHessDir`) and `|B_mer w| ≤ 4|B||w|`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `|DV_j(x) w| ≤ e^{-|x_j|²/(4a)} (1 + |x_j|²) |w|` for `a ≥ 1`. -/
theorem rc_fderiv_Vj_le (ν s : ℝ) (ha1 : 1 ≤ ageA ν s) (j : ℤ) (x w : ℝ × ℝ) :
    ‖fderiv ℝ (Vj ν s j) x w‖ ≤
      Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) * (1 + sq2 (xj ν j x)) * ‖w‖ := by
  have ha0 : 0 < ageA ν s := by linarith
  refine (gp_fderiv_Vj_norm ν s ha0 j x w).trans ?_
  have hκ0 : 0 ≤ (ageA ν s ^ 2)⁻¹ := by positivity
  have hκ : (ageA ν s ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith)
  have hE0 : 0 ≤ Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) := (Real.exp_pos _).le
  have hrS : ‖xj ν j x‖ ^ 2 ≤ sq2 (xj ν j x) := hu_norm_sq_le _
  have hra : ‖xj ν j x‖ ^ 2 / ageA ν s ≤ sq2 (xj ν j x) :=
    (div_le_self (sq_nonneg _) ha1).trans hrS
  have h1' : (ageA ν s ^ 2)⁻¹ * Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) ≤
      Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) := by
    have := mul_le_mul_of_nonneg_right hκ hE0
    linarith
  have h2' : 1 + ‖xj ν j x‖ ^ 2 / ageA ν s ≤ 1 + sq2 (xj ν j x) := by linarith
  exact mul_le_mul_of_nonneg_right (mul_le_mul h1' h2' (by positivity) hE0) (norm_nonneg _)

theorem rcBrkDerivPointwise : RcBrkDerivPointwise := by
  obtain ⟨K, hK, hH⟩ := rcHessDir
  refine ⟨8 + 4 * K, by positivity, ?_⟩
  intro ν s B j x v hν hν1 hs hsT
  have ha1 : 1 ≤ ageA ν s := by unfold ageA; nlinarith [mul_pos hν hs]
  set E := Real.exp (-(sq2 (xj ν j x)) / (4 * ageA ν s)) with hEdef
  set S := sq2 (xj ν j x) with hSdef
  set F := frob B with hFdef
  set r := ‖xj ν j x‖ with hrdef
  set n := ‖v‖ with hndef
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hF0 : 0 ≤ F := Real.sqrt_nonneg _
  have hn0 : 0 ≤ n := norm_nonneg _
  have hr0 : 0 ≤ r := norm_nonneg _
  have hrS : r ^ 2 ≤ S := hu_norm_sq_le _
  have hS0 : 0 ≤ S := le_trans (sq_nonneg r) hrS
  have hr1 : r ≤ 1 + S := by nlinarith [sq_nonneg (r - 1)]
  have hP1 : 1 ≤ 1 + S := by linarith
  have hP3 : 1 + S ≤ (1 + S) ^ 3 := by nlinarith [mul_le_mul hP1 hP1 zero_le_one (by linarith)]
  have t1 : ‖merApply B (fderiv ℝ (Vj ν s j) x v)‖ ≤ 4 * F * (E * (1 + S) * n) :=
    (rc_merApply_le B _).trans
      (mul_le_mul_of_nonneg_left (rc_fderiv_Vj_le ν s ha1 j x v) (by positivity))
  have t2 : ‖fderiv ℝ (Vj ν s j) x (merApply B v)‖ ≤ E * (1 + S) * (4 * F * n) :=
    (rc_fderiv_Vj_le ν s ha1 j x _).trans
      (mul_le_mul_of_nonneg_left (rc_merApply_le B v) (by positivity))
  have t3 : ‖fderiv ℝ (fderiv ℝ (Vj ν s j)) x v (merApply B (xj ν j x))‖ ≤
      K * (1 + S) ^ 2 * E * n * (4 * F * r) :=
    (hH ν s j x v _ hν hν1 hs hsT).trans
      (mul_le_mul_of_nonneg_left (rc_merApply_le B _) (by positivity))
  rw [rc_brk_fderiv]
  have hsum := (norm_sub_le _ _).trans (add_le_add t1 ((norm_add_le _ _).trans (add_le_add t2 t3)))
  refine hsum.trans ?_
  have u1 : 4 * F * (E * (1 + S) * n) ≤ 4 * F * (E * (1 + S) ^ 3 * n) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hP3 hE0) hn0
  have u2 : K * (1 + S) ^ 2 * E * n * (4 * F * r) ≤ K * (1 + S) ^ 2 * E * n * (4 * F * (1 + S)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hr1 (by positivity)) (by positivity)
  have e1 : E * (1 + S) * (4 * F * n) = 4 * F * (E * (1 + S) * n) := by ring
  have e2 : K * (1 + S) ^ 2 * E * n * (4 * F * (1 + S)) = 4 * K * F * (1 + S) ^ 3 * E * n := by
    ring
  nlinarith

end UnforcedLeray.Short.PartIIIb.Concrete
