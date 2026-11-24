import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Sub.FarMajorantL2.Defs

/-!
# Norm of the Cartesian lift off the axis (source 2675-2683)

Off the axis the frame `cylFrame z` is a rotation scaled by `√(z₀²+z₁²)/|z'|`, so the Frobenius
norm of `cylFrame z · (s • M) · (cylFrame z)ᵀ` is `s · |M|` for `s ≥ 0`.  The invariance is an
explicit polynomial identity in the entries, closed by `hab : a² + b² = 1`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

/-- The planar rotation-scaling `(a,b)` preserves the Frobenius sum of squares when `a²+b²=1`. -/
theorem polarRot_sumsq (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) (M : Matrix (Fin 3) (Fin 3) ℝ) :
    ∑ i, ∑ j, ((!![a, -b, 0; b, a, 0; 0, 0, 1] * M * !![a, b, 0; -b, a, 0; 0, 0, 1]) i j) ^ 2 =
      ∑ i, ∑ j, M i j ^ 2 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const, Matrix.tail_cons]
  linear_combination
    ((a ^ 2 + b ^ 2 + 1) * (M 0 0 ^ 2 + M 0 1 ^ 2 + M 1 0 ^ 2 + M 1 1 ^ 2) +
      (M 0 2 ^ 2 + M 1 2 ^ 2 + M 2 0 ^ 2 + M 2 1 ^ 2)) * hab

/-- Scaled rotation about the vertical axis: the Frobenius norm of `Q (s•M) Qᵀ` is `s |M|`. -/
theorem polarRot_scaled (a b s : ℝ) (hab : a ^ 2 + b ^ 2 = 1) (hs : 0 ≤ s)
    (M : Matrix (Fin 3) (Fin 3) ℝ) :
    UnforcedLeray.Short.IIIa.tensorNorm
        (!![a, -b, 0; b, a, 0; 0, 0, 1] * (s • M) * !![a, b, 0; -b, a, 0; 0, 0, 1]) =
      s * UnforcedLeray.Short.IIIa.tensorNorm M := by
  unfold UnforcedLeray.Short.IIIa.tensorNorm
  rw [Matrix.mul_smul, Matrix.smul_mul]
  have hX := polarRot_sumsq a b hab M
  simp only [Matrix.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum]
  rw [hX, Real.sqrt_mul (sq_nonneg s), Real.sqrt_sq hs]

theorem cartLiftNormOffAxis_holds : CartLiftNormOffAxis := by
  intro R c f τ z hz
  have hsq : UnforcedLeray.Short.PartIIIb.NearInst.hRad z ^ 2 = z 0 ^ 2 + z 1 ^ 2 := by
    unfold UnforcedLeray.Short.PartIIIb.NearInst.hRad
    exact Real.sq_sqrt (by positivity)
  have hab : (z 0 / UnforcedLeray.Short.PartIIIb.NearInst.hRad z) ^ 2 +
      (z 1 / UnforcedLeray.Short.PartIIIb.NearInst.hRad z) ^ 2 = 1 := by
    rw [div_pow, div_pow, ← add_div, ← hsq, div_self (pow_ne_zero 2 hz)]
  have hC : UnforcedLeray.Short.PartIIIb.NearInst.cylFrame z =
      !![z 0 / UnforcedLeray.Short.PartIIIb.NearInst.hRad z,
        -(z 1 / UnforcedLeray.Short.PartIIIb.NearInst.hRad z), 0;
        z 1 / UnforcedLeray.Short.PartIIIb.NearInst.hRad z,
        z 0 / UnforcedLeray.Short.PartIIIb.NearInst.hRad z, 0; 0, 0, 1] := by
    unfold UnforcedLeray.Short.PartIIIb.NearInst.cylFrame
    rfl
  have hT : (UnforcedLeray.Short.PartIIIb.NearInst.cylFrame z).transpose =
      !![z 0 / UnforcedLeray.Short.PartIIIb.NearInst.hRad z,
        z 1 / UnforcedLeray.Short.PartIIIb.NearInst.hRad z, 0;
        -(z 1 / UnforcedLeray.Short.PartIIIb.NearInst.hRad z),
        z 0 / UnforcedLeray.Short.PartIIIb.NearInst.hRad z, 0; 0, 0, 1] := by
    rw [hC]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hs : 0 ≤ (UnforcedLeray.Short.PartIIIb.NearInst.chartOf R c z τ).1 := by
    show 0 ≤ R ^ 2 / UnforcedLeray.Short.PartIIIb.NearInst.hRad z ^ 2
    positivity
  unfold UnforcedLeray.Short.IIIa.srcNorm gAx
  congr 1
  show UnforcedLeray.Short.IIIa.tensorNorm
      (UnforcedLeray.Short.PartIIIb.NearInst.cylFrame z *
        ((UnforcedLeray.Short.PartIIIb.NearInst.chartOf R c z τ).1 •
          UnforcedLeray.Short.PartIIIb.NearInst.nsSym (f (UnforcedLeray.Short.PartIIIb.NearInst.chartOf R c z τ))) *
        (UnforcedLeray.Short.PartIIIb.NearInst.cylFrame z).transpose) = _
  rw [hT, hC]
  exact polarRot_scaled _ _ _ hab hs _

end UnforcedLeray.Short.PartIIIb.NearInst.Masked
