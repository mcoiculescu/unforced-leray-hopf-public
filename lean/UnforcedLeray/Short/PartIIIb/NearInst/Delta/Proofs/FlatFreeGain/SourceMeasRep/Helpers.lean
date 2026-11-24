import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.FlatFreeGain.hh7.Props

/-!
Helpers for `SourceMeasRep` (item `PartIII-b:C/near/delta/7/2`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set Filter
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Delta

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst

theorem blk_norm_le (T : Ten3) :
    UnforcedLeray.Short.IIIa.tnorm2 (fun i j => ((nsSym T (merIdx i) (merIdx j) : ℝ) : ℂ)) ≤
      ‖T‖ := by
  unfold UnforcedLeray.Short.IIIa.tnorm2
  rw [EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  have key : ∀ x : ℝ, ‖((x : ℝ) : ℂ)‖ ^ 2 = x ^ 2 := fun x => by
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  simp only [Fin.sum_univ_two, Fintype.sum_prod_type, Fin.sum_univ_three, merIdx, nsSym, symRZ,
    key, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_fin_one, Matrix.cons_val_two,
    Matrix.tail_cons, Real.norm_eq_abs, sq_abs]
  nlinarith [sq_nonneg (T (0, 2) - T (2, 0)), sq_nonneg (T (0, 1)), sq_nonneg (T (1, 0)),
    sq_nonneg (T (1, 1)), sq_nonneg (T (1, 2)), sq_nonneg (T (2, 1))]

theorem nsSym_smul (k : ℝ) (T : Ten3) (i j : Fin 2) :
    nsSym (k • T) (merIdx i) (merIdx j) = k * nsSym T (merIdx i) (merIdx j) := by
  fin_cases i <;> fin_cases j <;> simp [nsSym, symRZ, merIdx, PiLp.smul_apply, smul_eq_mul] <;> ring

theorem conj_blk (k : ℝ) (hk : k ≠ 0) (T : Ten3) :
    k⁻¹ • (fun i j => ((nsSym (k • T) (merIdx i) (merIdx j) : ℝ) : ℂ)) =
      fun i j => ((nsSym T (merIdx i) (merIdx j) : ℝ) : ℂ) := by
  funext i j
  simp only [Pi.smul_apply, nsSym_smul]
  rw [Complex.real_smul]
  have hk' : (k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hk
  push_cast
  field_simp

end UnforcedLeray.Short.PartIIIb.NearInst.Delta
