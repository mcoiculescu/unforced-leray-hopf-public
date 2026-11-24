import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_2_3

/-!
# Reflection equivariance of `oldPhys` (`PartIII-b:IIIb-D2/3/1/2/3/4`)

Source of record: `the November 2 reference manuscript` lines 2666-2683.
For `z' = Fz` with `F = reflM` (`y₁ ↦ -y₁`): `hRad z' = hRad z`, `chartOf` is unchanged,
`cylFrame z' = F * cylFrame z * F` entrywise, and `F * nsSym T * F = nsSym T`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

lemma refl_z0 (z : Space) : actM reflM z 0 = z 0 := by
  simp [actM, reflM, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

lemma refl_z1 (z : Space) : actM reflM z 1 = - z 1 := by
  simp [actM, reflM, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

lemma refl_z2 (z : Space) : actM reflM z 2 = z 2 := by
  simp [actM, reflM, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

lemma refl_hRad (z : Space) : NearInst.hRad (actM reflM z) = NearInst.hRad z := by
  unfold NearInst.hRad
  rw [refl_z0, refl_z1]
  congr 1
  ring

lemma refl_chart (R c : ℝ) (z : Space) (τ : ℝ) :
    NearInst.chartOf R c (actM reflM z) τ = NearInst.chartOf R c z τ := by
  unfold NearInst.chartOf
  rw [refl_hRad z, refl_z2]

lemma refl_cyl (z : Space) :
    NearInst.cylFrame (actM reflM z) = reflM * NearInst.cylFrame z * reflM := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [NearInst.cylFrame, refl_hRad z, refl_z0, refl_z1, refl_z2,
      Matrix.mul_apply, Fin.sum_univ_three] <;>
    simp only [reflM, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Matrix.empty_val',
      Matrix.cons_val_fin_one, Matrix.head_fin_const] <;> ring

lemma reflM_transpose : reflM.transpose = reflM := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [reflM]

lemma refl_sym (s : ℝ) (T : Ten3) :
    reflM * (s • NearInst.nsSym T) * reflM = s • NearInst.nsSym T := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [NearInst.nsSym, reflM, Matrix.mul_apply, Fin.sum_univ_three]

lemma refl_conj (C X : Matrix (Fin 3) (Fin 3) ℝ) (hX : reflM * X * reflM = X) :
    reflM * C * reflM * X * (reflM * C * reflM).transpose =
      reflM * (C * X * C.transpose) * reflM.transpose := by
  rw [Matrix.transpose_mul, Matrix.transpose_mul, reflM_transpose]
  calc reflM * C * reflM * X * (reflM * (C.transpose * reflM))
      = reflM * C * (reflM * X * reflM) * (C.transpose * reflM) := by
        simp only [Matrix.mul_assoc]
    _ = reflM * C * X * (C.transpose * reflM) := by rw [hX]
    _ = reflM * (C * X * C.transpose) * reflM := by simp only [Matrix.mul_assoc]

/-- **Reflection equivariance of `oldPhys`** (`PartIII-b:IIIb-D2/3/1/2/3/4`). -/
theorem oldPhysReflEquiv : OldPhysReflEquiv := by
  intro R c g τ z
  simp only [oldPhys, NearInst.cartLift]
  rw [refl_chart R c z τ, refl_cyl z]
  exact refl_conj _ _ (refl_sym _ _)

end UnforcedLeray.Short.PartIIIb.Concrete
