import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_2_3

/-!
# Rotation equivariance of `oldPhys` (`PartIII-b:IIIb-D2/3/1/2/3/3`)

Source of record: `the November 2 reference manuscript` lines 2666-2683.
`oldPhys R c g τ z = NearInst.cartLift R c g τ z` (`PartIII-b/NearInst/Chart.lean:111`).
For `z' = Rz`, `hRad z' = hRad z`, `chartOf` is unchanged, and `cylFrame z' = R * cylFrame z`.
The identity then follows from associativity of matrix multiplication.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

lemma rot_z0 (co si : ℝ) (z : Space) : actM (rotM co si) z 0 = co * z 0 - si * z 1 := by
  simp [actM, rotM, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring

lemma rot_z1 (co si : ℝ) (z : Space) : actM (rotM co si) z 1 = si * z 0 + co * z 1 := by
  simp [actM, rotM, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring

lemma rot_z2 (co si : ℝ) (z : Space) : actM (rotM co si) z 2 = z 2 := by
  simp [actM, rotM, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

lemma rot_hRad (co si : ℝ) (hco : co ^ 2 + si ^ 2 = 1) (z : Space) :
    NearInst.hRad (actM (rotM co si) z) = NearInst.hRad z := by
  unfold NearInst.hRad
  rw [rot_z0, rot_z1]
  congr 1
  linear_combination (z 0 ^ 2 + z 1 ^ 2) * hco

lemma rot_chart (R c : ℝ) (co si : ℝ) (hco : co ^ 2 + si ^ 2 = 1) (z : Space) (τ : ℝ) :
    NearInst.chartOf R c (actM (rotM co si) z) τ = NearInst.chartOf R c z τ := by
  unfold NearInst.chartOf
  rw [rot_hRad co si hco z, rot_z2]

lemma rot_cyl (co si : ℝ) (hco : co ^ 2 + si ^ 2 = 1) (z : Space) :
    NearInst.cylFrame (actM (rotM co si) z) = rotM co si * NearInst.cylFrame z := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [NearInst.cylFrame, rot_hRad co si hco z, rot_z0, rot_z1, rot_z2,
      Matrix.mul_apply, Fin.sum_univ_three] <;>
    simp only [rotM, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Matrix.empty_val',
      Matrix.cons_val_fin_one, Matrix.head_fin_const, Matrix.of_apply] <;> ring

/-- **Rotation equivariance of `oldPhys`** (`PartIII-b:IIIb-D2/3/1/2/3/3`). -/
theorem oldPhysRotEquiv : OldPhysRotEquiv := by
  intro co si hco R c g τ z
  simp only [oldPhys, NearInst.cartLift]
  rw [rot_chart R c co si hco z τ, rot_cyl co si hco z]
  simp only [Matrix.transpose_mul, Matrix.mul_assoc]

end UnforcedLeray.Short.PartIIIb.Concrete
