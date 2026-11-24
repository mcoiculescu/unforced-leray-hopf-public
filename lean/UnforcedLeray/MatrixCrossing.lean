import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

/-!
# Finite-dimensional determinant crossing

The elementary real two-dimensional argument used in `paper/main.tex`,
`eq:st18-t00766`--`eq:st18-t00769`. These results retain continuity,
endpoint signs and Gram invertibility as explicit hypotheses. They do not
establish those hypotheses for the manuscript's reduced operator, nor
construct a Navier--Stokes background or mode.
-/

noncomputable section
open Set Matrix
namespace UnforcedLeray.MatrixCrossing

abbrev Matrix2 := Matrix (Fin 2) (Fin 2) ℝ
abbrev Vector2 := Fin 2 → ℝ

/-- The actual outer product of two real two-dimensional coordinate vectors. -/
def outerProduct (a b : Vector2) : Matrix2 := fun i j => a i * b j

/-- The rank-one determinant identity used in the spectral crossing. -/
theorem det_one_sub_outerProduct (a b : Vector2) :
    (1 - outerProduct a b).det = 1 - (outerProduct a b).trace := by
  simp [Matrix.det_fin_two, Matrix.trace_fin_two, outerProduct, Matrix.sub_apply]
  ring

/-- An invertible Gram factor cannot create a zero determinant. -/
theorem det_eq_zero_of_mul_gram (B G : Matrix2)
    (hG : G.det ≠ 0) (hBG : (B * G).det = 0) : B.det = 0 := by
  rw [Matrix.det_mul] at hBG
  exact (mul_eq_zero.mp hBG).resolve_right hG

/-- A real matrix path with strictly opposite endpoint signs is singular at
some interior parameter. -/
theorem exists_interior_det_zero (A : ℝ → Matrix2) {a b : ℝ}
    (hab : a < b) (hA : ContinuousOn A (Icc a b))
    (ha : (A a).det < 0) (hb : 0 < (A b).det) :
    ∃ x ∈ Ioo a b, (A x).det = 0 := by
  have hd : ContinuousOn (fun x => (A x).det) (Icc a b) :=
    continuous_id.matrix_det.comp_continuousOn hA
  obtain ⟨x, hx, hdet⟩ := intermediate_value_Icc hab.le hd ⟨ha.le, hb.le⟩
  have hxa : x ≠ a := by
    intro h
    subst x
    linarith
  have hxb : x ≠ b := by
    intro h
    subst x
    linarith
  exact ⟨x, ⟨lt_of_le_of_ne hx.1 hxa.symm, lt_of_le_of_ne hx.2 hxb⟩, hdet⟩

/-- A determinant crossing supplies a genuine nonzero real kernel vector. -/
theorem exists_interior_kernel (A : ℝ → Matrix2) {a b : ℝ}
    (hab : a < b) (hA : ContinuousOn A (Icc a b))
    (ha : (A a).det < 0) (hb : 0 < (A b).det) :
    ∃ x ∈ Ioo a b, ∃ v : Vector2, v ≠ 0 ∧ A x *ᵥ v = 0 := by
  obtain ⟨x, hx, hdet⟩ := exists_interior_det_zero A hab hA ha hb
  obtain ⟨v, hv, hAv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  exact ⟨x, hx, v, hv, hAv⟩

/-- The exact Gram-weighted crossing produces a nonzero vector in the kernel
of B itself, with the same fixed parameter. -/
theorem exists_interior_kernel_of_gram_crossing (B G : ℝ → Matrix2) {a b : ℝ}
    (hab : a < b) (hBG : ContinuousOn (fun x => B x * G x) (Icc a b))
    (ha : (B a * G a).det < 0) (hb : 0 < (B b * G b).det)
    (hG : ∀ x ∈ Icc a b, (G x).det ≠ 0) :
    ∃ x ∈ Ioo a b, ∃ v : Vector2, v ≠ 0 ∧ B x *ᵥ v = 0 := by
  obtain ⟨x, hx, hdet⟩ := exists_interior_det_zero (fun x => B x * G x) hab hBG ha hb
  have hB : (B x).det = 0 :=
    det_eq_zero_of_mul_gram (B x) (G x) (hG x ⟨hx.1.le, hx.2.le⟩) hdet
  obtain ⟨v, hv, hBv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hB
  exact ⟨x, hx, v, hv, hBv⟩

end UnforcedLeray.MatrixCrossing
