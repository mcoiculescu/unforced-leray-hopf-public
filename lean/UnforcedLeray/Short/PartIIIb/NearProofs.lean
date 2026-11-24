import UnforcedLeray.Short.PartIIIb.Near
import UnforcedLeray.Lib.AlgBlocks.Neumann

/-!
# Proofs of the operator statements of `Near.lean` (lines 4056-4062, 4126-4132)

`forcedColumnComparison` : the resolvent step for the forced column.
`nearInverseComparison`  : the geometric inverse series, from `Algebra.neumann_half`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Filter Topology Set

namespace UnforcedLeray.Short.PartIIIb

section

variable {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]

theorem conjG_apply (G : Z ≃L[ℝ] Z) (X : Z →L[ℝ] Z) (z : Z) :
    conjG G X z = G.symm (X (G z)) := rfl

theorem conjG_mul (G : Z ≃L[ℝ] Z) (X Y : Z →L[ℝ] Z) :
    conjG G (X * Y) = conjG G X * conjG G Y := by
  ext z
  simp [conjG_apply]

theorem conjG_one (G : Z ≃L[ℝ] Z) : conjG G (1 : Z →L[ℝ] Z) = 1 := by
  ext z; simp [conjG_apply]

theorem conjG_sub (G : Z ≃L[ℝ] Z) (X Y : Z →L[ℝ] Z) :
    conjG G (X - Y) = conjG G X - conjG G Y := by
  ext z; simp [conjG_apply]

/-- Inverse conjugation. -/
def conjG' (G : Z ≃L[ℝ] Z) (X : Z →L[ℝ] Z) : Z →L[ℝ] Z :=
  (G : Z →L[ℝ] Z) ∘L X ∘L (G.symm : Z →L[ℝ] Z)

theorem conjG'_conjG (G : Z ≃L[ℝ] Z) (X : Z →L[ℝ] Z) : conjG' G (conjG G X) = X := by
  ext z; simp [conjG', conjG_apply]

theorem conjG_conjG' (G : Z ≃L[ℝ] Z) (X : Z →L[ℝ] Z) : conjG G (conjG' G X) = X := by
  ext z; simp [conjG', conjG_apply]

theorem conjG'_mul (G : Z ≃L[ℝ] Z) (X Y : Z →L[ℝ] Z) :
    conjG' G (X * Y) = conjG' G X * conjG' G Y := by
  ext z; simp [conjG']

theorem conjG'_sub (G : Z ≃L[ℝ] Z) (X Y : Z →L[ℝ] Z) :
    conjG' G (X - Y) = conjG' G X - conjG' G Y := by
  ext z; simp [conjG']

theorem conjG'_one (G : Z ≃L[ℝ] Z) : conjG' G (1 : Z →L[ℝ] Z) = 1 := by
  ext z; simp [conjG']

end

theorem forcedColumnComparison : ForcedColumnComparison := by
  intro Z _ _ _ G Dinv D₀inv u u₀ Q δ h1 h2
  have e : G.symm (Dinv u - D₀inv u₀) =
      conjG G Dinv (G.symm (u - u₀)) + conjG G (Dinv - D₀inv) (G.symm u₀) := by
    simp [conjG_apply, map_sub]
  rw [e]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right h1 (norm_nonneg _))
  · exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right h2 (norm_nonneg _))

theorem nearInverseComparison : NearInverseComparison := by
  intro Z _ _ _ G D₀ D₀inv DN Q δ hl hr hQ hδ hQδ
  set a : Z →L[ℝ] Z := conjG G D₀ with ha
  set b : Z →L[ℝ] Z := conjG G DN with hb
  have hamul1 : conjG G D₀inv * a = 1 := by
    rw [ha, ← conjG_mul, ← conjG_one G]; exact congrArg (conjG G) hl
  have hamul2 : a * conjG G D₀inv = 1 := by
    rw [ha, ← conjG_mul, ← conjG_one G]; exact congrArg (conjG G) hr
  have hunit : IsUnit a := ⟨⟨a, conjG G D₀inv, hamul2, hamul1⟩, rfl⟩
  have hinv : Ring.inverse a = conjG G D₀inv :=
    Algebra.inverse_eq_of_mul_eq_one hamul2 hamul1
  have hb_sub : b - a = conjG G (DN - D₀) := by rw [hb, ha, conjG_sub]
  have h1 : ‖(1 : Z →L[ℝ] Z)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have hQ' : ‖Ring.inverse a‖ ≤ Q := by rw [hinv]; exact hQ
  have hδ' : ‖b - a‖ ≤ δ := by rw [hb_sub]; exact hδ
  obtain ⟨hbu, hb1, hb2⟩ := Algebra.neumann_half h1 hunit hQ' hδ' hQδ.le
  refine ⟨conjG' G (Ring.inverse b), ?_, ?_, ?_, ?_⟩
  · have : Ring.inverse b * b = 1 := by
      exact Ring.inverse_mul_cancel b hbu
    have h := congrArg (conjG' G) this
    rw [conjG'_mul, conjG'_one, hb, conjG'_conjG] at h
    exact h
  · have : b * Ring.inverse b = 1 := by
      exact Ring.mul_inverse_cancel b hbu
    have h := congrArg (conjG' G) this
    rw [conjG'_mul, conjG'_one, hb, conjG'_conjG] at h
    exact h
  · rw [conjG_conjG']; exact hb1
  · rw [conjG_sub, conjG_conjG', ← hinv]; exact hb2

end UnforcedLeray.Short.PartIIIb
