import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_inst_10_3
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.EATermSummable.Hess

/-!
# `PartIII-b:C/inst/10/3` leaf E1a: uniform second derivatives of `V_j` (source 4963-4966, 4978)

`V_j = a⁻² e^{-|x_j|²/(4a)} J x_j` with `a = ageA ν s ≥ 1`. The explicit first derivative
`hsG` and the line derivative `hs_line` come from `Hess.lean`; the scalar prefactor
`hsE = a⁻² e^{-|x_j|²/(4a)}` keeps the full Gaussian exponent, and the polynomial coefficient is
bounded using `a ≥ 1` and `|x_j|_∞² ≤ |x_j|²`.
-/

set_option autoImplicit false

noncomputable section

open Real

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Sup-norm squared is at most the Euclidean square `sq2`. -/
lemma hu_norm_sq_le (y : ℝ × ℝ) : ‖y‖ ^ 2 ≤ sq2 y := by
  unfold sq2
  rw [Prod.norm_def]
  have h1 : ‖y.1‖ ^ 2 = y.1 ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
  have h2 : ‖y.2‖ ^ 2 = y.2 ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
  rcases le_total ‖y.1‖ ‖y.2‖ with h | h
  · rw [max_eq_right h]
    nlinarith [sq_nonneg y.1]
  · rw [max_eq_left h]
    nlinarith [sq_nonneg y.2]

/-- `sq2` is nonnegative. -/
lemma hu_sq2_nonneg (y : ℝ × ℝ) : 0 ≤ sq2 y := by
  unfold sq2; positivity

/-- Polynomial coefficient bound: `3 n / a + n³ / a² ≤ 4 (1 + sq2)²` for `a ≥ 1`. -/
lemma hu_poly_bound (n a S Q : ℝ) (hn : 0 ≤ n) (ha : 1 ≤ a) (hQ : 0 ≤ Q)
    (hnQ : n ^ 2 ≤ Q) (hS : S = 1 + Q) : 3 * n / a + n ^ 3 / a ^ 2 ≤ 4 * S ^ 2 := by
  have ha0 : 0 < a := by linarith
  have ha2 : 1 ≤ a ^ 2 := by nlinarith
  have hnS : n ≤ S := by rw [hS]; nlinarith [sq_nonneg (n - 1 / 2)]
  have hS1 : 1 ≤ S := by rw [hS]; linarith
  have hn3 : n ^ 3 ≤ S ^ 2 := by
    calc n ^ 3 = n * n ^ 2 := by ring
      _ ≤ S * Q := mul_le_mul hnS hnQ (sq_nonneg n) (by linarith)
      _ ≤ S * S := mul_le_mul_of_nonneg_left (by rw [hS]; linarith) (by linarith)
      _ = S ^ 2 := by ring
  have hA1 : n / a ≤ n := div_le_self hn ha
  have hA2 : n ^ 3 / a ^ 2 ≤ n ^ 3 := div_le_self (pow_nonneg hn 3) ha2
  have e : 3 * n / a = 3 * (n / a) := by ring
  have hSS : S ≤ S ^ 2 := by nlinarith
  rw [e]
  nlinarith

/-- Leaf E1a (source 4963-4966, 4978): uniform bound on the second derivatives of `V_j`. -/
theorem hessVjUnif : HessVjUnif := by
  refine ⟨4, by norm_num, ?_⟩
  intro ν s hν hν1 hs _ j x p b
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

end UnforcedLeray.Short.PartIIIb.Concrete
