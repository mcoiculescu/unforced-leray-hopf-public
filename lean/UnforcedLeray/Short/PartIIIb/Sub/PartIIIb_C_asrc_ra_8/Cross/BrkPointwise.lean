import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_asrc_ra_8.Cross.Defs
import UnforcedLeray.Short.PartIIIb.Sub.Leaves.CellTerm
import UnforcedLeray.Short.PartIIIb.Sub.Leaves.EAcHessUnif

/-!
# `PartIII-b:C/asrc/ra/8/2/org` : pointwise bound of the bracket `b_j`

Source `the November 2 reference manuscript`
4963-4972: `b_j = B_mer V_j - DV_j(B_mer x_j)`, `|V_j| = a⁻²e|x_j|`,
`|DV_j w| ≤ a⁻²e(1 + |x_j|²/a)|w|` (`gp_fderiv_Vj_norm`), `|B_mer w| ≤ 4|B||w|`; with `a ≥ 1`,
`|x_j|_∞² ≤ |x_j|²`: `|b_j| ≤ 8|B|(1+|x_j|²)² e^{-|x_j|²/(4a)}`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `|B_mer w| ≤ 4 |B| |w|`. -/
theorem rc_merApply_le (B : Mat3) (w : ℝ × ℝ) : ‖merApply B w‖ ≤ 4 * frob B * ‖w‖ := by
  have hM := gp_merApply_norm_le B w
  have hS1F : |B 0 0| + |B 0 2| + |B 2 0| + |B 2 2| ≤ 4 * frob B := by
    linarith [fAc_abs_le_frob B 0 0, fAc_abs_le_frob B 0 2, fAc_abs_le_frob B 2 0,
      fAc_abs_le_frob B 2 2]
  exact hM.trans (mul_le_mul_of_nonneg_right hS1F (norm_nonneg w))

theorem rcBrkPointwise : RcBrkPointwise := by
  refine ⟨8, by norm_num, ?_⟩
  intro ν s B j x hν hν1 hs hsT
  have ha0 : 0 < ageA ν s := by unfold ageA; nlinarith [mul_pos hν hs]
  have ha1 : 1 ≤ ageA ν s := by unfold ageA; nlinarith [mul_pos hν hs]
  set a := ageA ν s with hadef
  set E := Real.exp (-(sq2 (xj ν j x)) / (4 * a)) with hEdef
  set r := ‖xj ν j x‖ with hrdef
  set S := sq2 (xj ν j x) with hSdef
  set F := frob B with hFdef
  have hκ0 : 0 ≤ (a ^ 2)⁻¹ := by positivity
  have hκ : (a ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith)
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hr0 : 0 ≤ r := norm_nonneg _
  have hF0 : 0 ≤ F := Real.sqrt_nonneg _
  have hrS : r ^ 2 ≤ S := hu_norm_sq_le _
  have hS0 : 0 ≤ S := le_trans (sq_nonneg r) hrS
  have hr1 : r ≤ 1 + S := by nlinarith [sq_nonneg (r - 1)]
  have hra : r ^ 2 / a ≤ S := (div_le_self (sq_nonneg r) ha1).trans hrS
  -- the two parts
  have h1 : ‖merApply B (Vj ν s j x)‖ ≤ 4 * F * (E * r) := by
    refine (rc_merApply_le B _).trans ?_
    rw [gp_Vj_norm_eq]
    have : (a ^ 2)⁻¹ * E * r ≤ E * r := by
      have := mul_le_mul_of_nonneg_right hκ (mul_nonneg hE0 hr0)
      linarith [mul_assoc ((a ^ 2)⁻¹) E r]
    exact mul_le_mul_of_nonneg_left this (by positivity)
  have h2 : ‖fderiv ℝ (Vj ν s j) x (merApply B (xj ν j x))‖ ≤
      E * (1 + S) * (4 * F * r) := by
    refine (gp_fderiv_Vj_norm ν s ha0 j x _).trans ?_
    have hm := rc_merApply_le B (xj ν j x)
    have hq : (a ^ 2)⁻¹ * E * (1 + r ^ 2 / a) ≤ E * (1 + S) := by
      have h1' : (a ^ 2)⁻¹ * E ≤ E := by
        have := mul_le_mul_of_nonneg_right hκ hE0
        linarith
      have h2' : 1 + r ^ 2 / a ≤ 1 + S := by linarith
      exact mul_le_mul h1' h2' (by positivity) hE0
    exact mul_le_mul hq hm (norm_nonneg _) (by positivity)
  unfold rcBrk
  calc ‖merApply B (Vj ν s j x) - fderiv ℝ (Vj ν s j) x (merApply B (xj ν j x))‖
      ≤ ‖merApply B (Vj ν s j x)‖ + ‖fderiv ℝ (Vj ν s j) x (merApply B (xj ν j x))‖ :=
        norm_sub_le _ _
    _ ≤ 4 * F * (E * r) + E * (1 + S) * (4 * F * r) := add_le_add h1 h2
    _ ≤ 8 * F * (1 + S) ^ 2 * E := by
        have hA : E * r ≤ E * (1 + S) := mul_le_mul_of_nonneg_left hr1 hE0
        have hB : 4 * F * (E * r) ≤ 4 * F * (E * (1 + S) ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have : E * (1 + S) ≤ E * (1 + S) ^ 2 := by
            apply mul_le_mul_of_nonneg_left _ hE0
            nlinarith
          linarith
        have hC : E * (1 + S) * (4 * F * r) ≤ E * (1 + S) * (4 * F * (1 + S)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_left hr1 (by positivity)
        nlinarith

end UnforcedLeray.Short.PartIIIb.Concrete
