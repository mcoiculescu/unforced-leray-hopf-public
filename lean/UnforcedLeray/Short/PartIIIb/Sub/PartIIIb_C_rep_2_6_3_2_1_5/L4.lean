import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_6_3_2_1_5

/-!
# `LOpBound` (`PartIII-b:C/rep/2/6/3/2/1/5/4`)

Source `the November 2 reference manuscript`
lines 3603-3626, 3800-3807, 4171-4200.

Operator bound for `½ y·∇Φ + νΔΦ`: the first-order term is bounded by `‖iteratedFDeriv 1 Φ y‖`
and `‖y‖`, each second derivative `∂²Φ(e_l, e_l)` by `‖iteratedFDeriv 2 Φ y‖` (unit vectors).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem lOpBound : LOpBound := by
  intro ν Φ y hΦ
  have hfd : ContDiff ℝ 1 (fderiv ℝ Φ) := hΦ.fderiv_right (m := 1) (by norm_num)
  have hdiffFd : DifferentiableAt ℝ (fderiv ℝ Φ) y :=
    (hfd.differentiable (by norm_num)) y
  -- first derivative bound
  have hA : ‖fderiv ℝ Φ y y‖ ≤ ‖iteratedFDeriv ℝ 1 Φ y‖ * ‖y‖ := by
    have h := (iteratedFDeriv ℝ 1 Φ y).le_opNorm (fun _ : Fin 1 => y)
    simpa using h
  -- second derivative bound on the diagonal directions
  have hcoord : ∀ l : Fin 3, ‖UnforcedLeray.coordinateVector l‖ = 1 := fun l => by
    simp [UnforcedLeray.coordinateVector]
  have hD : ∀ l : Fin 3, ‖fderiv ℝ (fun y' => fderiv ℝ Φ y' (UnforcedLeray.coordinateVector l)) y
      (UnforcedLeray.coordinateVector l)‖ ≤ ‖iteratedFDeriv ℝ 2 Φ y‖ := by
    intro l
    have e1 : fderiv ℝ (fun y' => fderiv ℝ Φ y' (UnforcedLeray.coordinateVector l)) y
        (UnforcedLeray.coordinateVector l)
        = iteratedFDeriv ℝ 2 Φ y ![UnforcedLeray.coordinateVector l, UnforcedLeray.coordinateVector l] := by
      rw [iteratedFDeriv_two_apply]
      rw [fderiv_clm_apply hdiffFd (differentiableAt_const (UnforcedLeray.coordinateVector l))]
      simp
    rw [e1]
    have h := (iteratedFDeriv ℝ 2 Φ y).le_opNorm
      ![UnforcedLeray.coordinateVector l, UnforcedLeray.coordinateVector l]
    have hp : ∏ i : Fin 2, ‖(![UnforcedLeray.coordinateVector l, UnforcedLeray.coordinateVector l]
        : Fin 2 → Space) i‖ = 1 := by
      simp [Fin.prod_univ_two, hcoord l]
    rw [hp, mul_one] at h
    exact h
  have hS : ‖∑ l : Fin 3, fderiv ℝ (fun y' => fderiv ℝ Φ y' (UnforcedLeray.coordinateVector l)) y
      (UnforcedLeray.coordinateVector l)‖ ≤ 3 * ‖iteratedFDeriv ℝ 2 Φ y‖ := by
    refine (norm_sum_le _ _).trans ?_
    rw [Fin.sum_univ_three]
    linarith [hD 0, hD 1, hD 2]
  have hν0 : 0 ≤ |ν| := abs_nonneg _
  have hnu : ‖(ν : ℂ)‖ = |ν| := by
    rw [Complex.norm_real, Real.norm_eq_abs]
  have h12 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, h12, hnu]
  have t1 : 1 / 2 * ‖fderiv ℝ Φ y y‖ ≤ (‖y‖ / 2) * ‖iteratedFDeriv ℝ 1 Φ y‖ := by
    have := mul_le_mul_of_nonneg_left hA (by norm_num : (0 : ℝ) ≤ 1 / 2)
    linarith
  have t2 : |ν| * ‖∑ l : Fin 3, fderiv ℝ (fun y' => fderiv ℝ Φ y' (UnforcedLeray.coordinateVector l)) y
      (UnforcedLeray.coordinateVector l)‖ ≤ 3 * |ν| * ‖iteratedFDeriv ℝ 2 Φ y‖ := by
    have := mul_le_mul_of_nonneg_left hS hν0
    linarith
  linarith

end UnforcedLeray.Short.PartIIIb.Concrete
