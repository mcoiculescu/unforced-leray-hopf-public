import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Part II-b, helper for the graph transform: inverse of `a + b ∘ ξ`

Source: SP 2172-2188 (`short-bg:graphs`, the Lipschitz and invariance bounds). Task
`PartII-b:T05`, used by `T06`.

Write `a + b ∘ ξ = a (1 + a⁻¹ (b ∘ ξ))`. The perturbation `K = a⁻¹ (b ∘ ξ)` has
`‖K‖ ≤ A η r < 1`, so `1 + K` is a unit (`Units.oneSub`), and
`M = (1 + K)⁻¹ a⁻¹` is a two-sided inverse with `‖M‖ ≤ A / (1 - A η r)`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

/-- SP 2172-2188: if `a` has the two-sided inverse `ainv` with `‖ainv‖ ≤ A`, and `b ∘ ξ` is
small (`‖b‖ ≤ η`, `‖ξ‖ ≤ r`, `A η r < 1`), then `a + b ∘ ξ` has a two-sided inverse `M` with
`‖M‖ ≤ A / (1 - A η r)`. -/
theorem exists_inverse_add_comp {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] (a : E →L[ℝ] E)
    (ainv : E →L[ℝ] E) (b : F →L[ℝ] E) (ξ : E →L[ℝ] F) {A η r : ℝ} (h1 : ainv * a = 1)
    (h2 : a * ainv = 1) (hA : ‖ainv‖ ≤ A) (hb : ‖b‖ ≤ η) (hξ : ‖ξ‖ ≤ r) (hη : 0 ≤ η)
    (hr : 0 ≤ r) (hArη : A * η * r < 1) :
    ∃ M : E →L[ℝ] E, M * (a + b.comp ξ) = 1 ∧ (a + b.comp ξ) * M = 1 ∧
      ‖M‖ ≤ A / (1 - A * η * r) := by
  have hA0 : 0 ≤ A := le_trans (norm_nonneg _) hA
  -- the perturbation `K = ainv ∘ (b ∘ ξ)` satisfies `‖K‖ ≤ A η r`
  have hbξ : ‖b.comp ξ‖ ≤ η * r :=
    (b.opNorm_comp_le ξ).trans (mul_le_mul hb hξ (norm_nonneg _) hη)
  have hKn : ‖ainv * b.comp ξ‖ ≤ A * η * r := by
    have h := (norm_mul_le ainv (b.comp ξ)).trans (mul_le_mul hA hbξ (norm_nonneg _) hA0)
    rw [mul_assoc]
    exact h
  have hKn' : ‖-(ainv * b.comp ξ)‖ < 1 := by
    rw [norm_neg]
    linarith
  -- `1 + K` is a unit, with inverse `V`
  obtain ⟨V, hV1, hV2⟩ : ∃ V : E →L[ℝ] E, V * (1 + ainv * b.comp ξ) = 1 ∧
      (1 + ainv * b.comp ξ) * V = 1 := by
    refine ⟨↑(Units.oneSub (-(ainv * b.comp ξ)) hKn')⁻¹, ?_, ?_⟩
    · have h := (Units.oneSub (-(ainv * b.comp ξ)) hKn').inv_mul
      rw [Units.val_oneSub, sub_neg_eq_add] at h
      exact h
    · have h := (Units.oneSub (-(ainv * b.comp ξ)) hKn').mul_inv
      rw [Units.val_oneSub, sub_neg_eq_add] at h
      exact h
  -- `a + b ∘ ξ = a (1 + K)`
  have hT : a + b.comp ξ = a * (1 + ainv * b.comp ξ) := by
    rw [mul_add, mul_one, ← mul_assoc, h2, one_mul]
  have hMT : V * ainv * (a + b.comp ξ) = 1 := by
    rw [hT, mul_assoc V ainv, ← mul_assoc ainv a, h1, one_mul, hV1]
  have hTM : (a + b.comp ξ) * (V * ainv) = 1 := by
    rw [hT, mul_assoc a (1 + ainv * b.comp ξ) (V * ainv),
      ← mul_assoc (1 + ainv * b.comp ξ) V ainv, hV2, one_mul, h2]
  -- `‖V‖ (1 - A η r) ≤ 1`
  have hVn : ‖V‖ * (1 - A * η * r) ≤ 1 := by
    have hV3 : V = 1 - V * (ainv * b.comp ξ) := by
      have h : V * (1 + ainv * b.comp ξ) = V + V * (ainv * b.comp ξ) := by
        rw [mul_add, mul_one]
      rw [h] at hV1
      exact eq_sub_of_add_eq hV1
    have hn1 : ‖(1 : E →L[ℝ] E)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    have h4 : ‖V‖ ≤ ‖(1 : E →L[ℝ] E)‖ + ‖V * (ainv * b.comp ξ)‖ := by
      calc ‖V‖ = ‖(1 : E →L[ℝ] E) - V * (ainv * b.comp ξ)‖ := by rw [← hV3]
        _ ≤ ‖(1 : E →L[ℝ] E)‖ + ‖V * (ainv * b.comp ξ)‖ := norm_sub_le _ _
    have h5 : ‖V * (ainv * b.comp ξ)‖ ≤ ‖V‖ * ‖ainv * b.comp ξ‖ := norm_mul_le _ _
    have h6 : ‖V‖ * ‖ainv * b.comp ξ‖ ≤ ‖V‖ * (A * η * r) :=
      mul_le_mul_of_nonneg_left hKn (norm_nonneg V)
    nlinarith [norm_nonneg V]
  refine ⟨V * ainv, hMT, hTM, ?_⟩
  have hq : 0 < 1 - A * η * r := by linarith
  rw [le_div_iff₀ hq]
  have hM : ‖V * ainv‖ ≤ ‖V‖ * A :=
    (norm_mul_le V ainv).trans (mul_le_mul_of_nonneg_left hA (norm_nonneg V))
  calc ‖V * ainv‖ * (1 - A * η * r) ≤ ‖V‖ * A * (1 - A * η * r) :=
        mul_le_mul_of_nonneg_right hM hq.le
    _ = A * (‖V‖ * (1 - A * η * r)) := by ring
    _ ≤ A * 1 := mul_le_mul_of_nonneg_left hVn hA0
    _ = A := mul_one A

end UnforcedLeray.Short.IIb
