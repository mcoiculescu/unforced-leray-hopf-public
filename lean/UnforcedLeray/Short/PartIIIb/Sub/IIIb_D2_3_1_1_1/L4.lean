import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_1

/-!
# `CartLiftFrobBound` (source 2675, 2683)

`|cartLift R c G τ z|_F ≤ s |G(chartOf R c z τ)|_F` with `s = (chartOf R c z τ).1`:
the rotation `cylFrame z` is orthogonal (`a² + b² = 1`), `nsSym` does not increase the
Frobenius norm, and on the axis `s = 0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- Frobenius norm is invariant under the rotation `[[a,-b,0],[b,a,0],[0,0,1]]` with `a² + b² = 1`. -/
theorem l4_frob_rot (a b : ℝ) (h : a ^ 2 + b ^ 2 = 1) (M : Matrix (Fin 3) (Fin 3) ℝ) :
    ∑ i : Fin 3, ∑ j : Fin 3,
        ((!![a, -b, 0; b, a, 0; 0, 0, 1] * M * (!![a, -b, 0; b, a, 0; 0, 0, 1]).transpose) i j) ^ 2
      = ∑ i : Fin 3, ∑ j : Fin 3, M i j ^ 2 := by
  simp only [Fin.sum_univ_three, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const,
    Matrix.tail_cons]
  linear_combination
    ((a ^ 2 + b ^ 2 + 1) * (M 0 0 ^ 2 + M 1 0 ^ 2 + M 0 1 ^ 2 + M 1 1 ^ 2)
      + (M 2 0 ^ 2 + M 2 1 ^ 2) + (M 0 2 ^ 2 + M 1 2 ^ 2)) * h

/-- **Pointwise Frobenius bound of the lift** (source 2683: `𝒩_TT = sT` in the orthonormal frame;
`nsSym` does not increase the Frobenius norm): `|cartLift R c G τ z| ≤ s|G(chartOf R c z τ)|`,
`s = (chartOf R c z τ).1` (on the axis both sides vanish: `s = R²/0 = 0`). -/
theorem cartLiftFrobBound : CartLiftFrobBound := by
  intro R c G τ z
  have hs_def : (NearInst.chartOf R c z τ).1 = R ^ 2 / NearInst.hRad z ^ 2 := rfl
  have hs0 : 0 ≤ (NearInst.chartOf R c z τ).1 := by
    rw [hs_def]; positivity
  unfold oldPhys IIIa.tensorNorm
  unfold NearInst.cartLift
  set X := G (NearInst.chartOf R c z τ) with hX
  set s := (NearInst.chartOf R c z τ).1 with hsset
  rcases eq_or_ne (NearInst.hRad z) 0 with h0 | hne
  · have hs' : s = 0 := by
      rw [hs_def, h0]; simp
    rw [hs']
    simp
  · have hpos : 0 ≤ NearInst.hRad z := Real.sqrt_nonneg _
    have hh2 : NearInst.hRad z ^ 2 = z 0 ^ 2 + z 1 ^ 2 := by
      unfold NearInst.hRad
      exact Real.sq_sqrt (by positivity)
    have hab : (z 0 / NearInst.hRad z) ^ 2 + (z 1 / NearInst.hRad z) ^ 2 = 1 := by
      rw [div_pow, div_pow, ← add_div, ← hh2, div_self (pow_ne_zero 2 hne)]
    have hC : NearInst.cylFrame z =
        !![z 0 / NearInst.hRad z, -(z 1 / NearInst.hRad z), 0;
          z 1 / NearInst.hRad z, z 0 / NearInst.hRad z, 0; 0, 0, 1] := rfl
    have hXn : ‖X‖ = Real.sqrt (∑ i : Fin 3, ∑ j : Fin 3, X (i, j) ^ 2) := by
      rw [EuclideanSpace.norm_eq, Fintype.sum_prod_type]
      simp [Real.norm_eq_abs, sq_abs]
    have hnn : ∑ i : Fin 3, ∑ j : Fin 3, NearInst.nsSym X i j ^ 2
        ≤ ∑ i : Fin 3, ∑ j : Fin 3, X (i, j) ^ 2 := by
      simp [Fin.sum_univ_three, NearInst.nsSym, NearInst.symRZ]
      nlinarith [sq_nonneg (X (0, 2) - X (2, 0)), sq_nonneg (X (0, 1)), sq_nonneg (X (1, 0)),
        sq_nonneg (X (1, 2)), sq_nonneg (X (2, 1))]
    have hsum : ∑ i : Fin 3, ∑ j : Fin 3, (s • NearInst.nsSym X) i j ^ 2
        ≤ s ^ 2 * ∑ i : Fin 3, ∑ j : Fin 3, X (i, j) ^ 2 := by
      have e : ∑ i : Fin 3, ∑ j : Fin 3, (s • NearInst.nsSym X) i j ^ 2
          = s ^ 2 * ∑ i : Fin 3, ∑ j : Fin 3, NearInst.nsSym X i j ^ 2 := by
        simp only [Matrix.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]
      rw [e]
      exact mul_le_mul_of_nonneg_left hnn (sq_nonneg s)
    rw [hC, l4_frob_rot _ _ hab, hXn]
    have key : s * Real.sqrt (∑ i : Fin 3, ∑ j : Fin 3, X (i, j) ^ 2)
        = Real.sqrt (s ^ 2 * ∑ i : Fin 3, ∑ j : Fin 3, X (i, j) ^ 2) := by
      rw [Real.sqrt_mul (sq_nonneg s), Real.sqrt_sq hs0]
    rw [key]
    exact Real.sqrt_le_sqrt hsum

end UnforcedLeray.Short.PartIIIb.Concrete
