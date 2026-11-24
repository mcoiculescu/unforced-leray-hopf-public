import UnforcedLeray.Short.PartIIIb.MixedReturn
import UnforcedLeray.Lib.AlgBlocks.Neumann

/-!
# Proof of `MR_Reduce` (target `mrReduce`; source: `the November 2 reference manuscript`, lines 5744-5766)

Schur reduction at one frozen `z`.  Write `R̃ = R + A (I - C)⁻¹ B`, `q = r + h < 1`.

* `‖(I - C)⁻¹‖ ≤ (1 - c)⁻¹` (Neumann bound), hence `‖R̃‖ ≤ r + h` (`opNorm_comp_le`).
* `w = (I - R̃)⁻¹ a` satisfies `w = a + R̃ w`, and `‖w‖ ≤ (1 - q)⁻¹ ‖a‖`; so
  `ℓ w - ℓ a = ℓ (R̃ w)` and `|ℓ w - ℓ a| ≤ ‖ℓ‖ q (1 - q)⁻¹ ‖a‖`.
* If `ℓ w = 1`: `w ≠ 0`; `y = (I - C)⁻¹ B w` satisfies `y = B w + C y`; and
  `w = a + R̃ w = ℓ w • a + R w + A y`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb

/-- Pointwise value of `1` on a real normed space (definitional). -/
theorem mrRed_one_apply {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (x : V) :
    (1 : V →L[ℝ] V) x = x := rfl

/-- Pointwise value of a difference of continuous linear maps (definitional). -/
theorem mrRed_sub_apply {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (f g : V →L[ℝ] V)
    (x : V) : (f - g) x = f x - g x := rfl

/-- Pointwise value of the Schur complement `R̃ = R + A (I - C)⁻¹ B` (definitional). -/
theorem mrRed_schurTilde_apply {E X : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (A : X →L[ℝ] E) (B : E →L[ℝ] X) (C : X →L[ℝ] X) (R : E →L[ℝ] E) (w : E) :
    schurTilde A B C R w = R w + A (Ring.inverse (1 - C) (B w)) := rfl

/-- `MR_Reduce`, lines 5757-5766 of the source: the Schur reduction and deviation bound at a
frozen `z`. -/
theorem mrReduce : UnforcedLeray.Short.PartIIIb.MR_Reduce := by
  unfold UnforcedLeray.Short.PartIIIb.MR_Reduce
  intro E X hEg hEs hEc hXg hXs hXc A B C R a ℓ c r h hCc hc1 hRr hAB hrh
  -- basic sign and size facts
  have hC1 : ‖C‖ < 1 := lt_of_le_of_lt hCc hc1
  have hr0 : 0 ≤ r := (norm_nonneg _).trans hRr
  have hh0 : 0 ≤ h := by
    have h0 := div_nonneg (mul_nonneg (norm_nonneg A) (norm_nonneg B))
      (le_of_lt (sub_pos.mpr hc1))
    linarith
  have hq0 : 0 ≤ r + h := by linarith
  -- norm of the identity is at most one
  have honeE : ‖(1 : E →L[ℝ] E)‖ ≤ 1 := by
    rw [ContinuousLinearMap.one_def]
    exact ContinuousLinearMap.norm_id_le
  have honeX : ‖(1 : X →L[ℝ] X)‖ ≤ 1 := by
    rw [ContinuousLinearMap.one_def]
    exact ContinuousLinearMap.norm_id_le
  -- the inverse of I - C
  have hCu : IsUnit (1 - C) := UnforcedLeray.Algebra.isUnit_one_sub hC1
  have hMn : ‖Ring.inverse (1 - C)‖ ≤ (1 - c)⁻¹ := by
    refine (UnforcedLeray.Algebra.norm_inverse_one_sub_le honeX hC1).trans ?_
    exact inv_anti₀ (by linarith) (by linarith)
  -- Part 1: ‖R̃‖ ≤ r + h
  have hRt : ‖schurTilde A B C R‖ ≤ r + h := by
    have hcomp : ‖A ∘L Ring.inverse (1 - C) ∘L B‖ ≤ ‖A‖ * ((1 - c)⁻¹ * ‖B‖) := by
      refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
      exact mul_le_mul_of_nonneg_right hMn (norm_nonneg _)
    have hfrac : ‖A‖ * ((1 - c)⁻¹ * ‖B‖) = ‖A‖ * ‖B‖ / (1 - c) := by ring
    unfold schurTilde
    refine (norm_add_le _ _).trans (add_le_add hRr ?_)
    linarith
  have hRt1 : ‖schurTilde A B C R‖ < 1 := lt_of_le_of_lt hRt hrh
  have hu : IsUnit (1 - schurTilde A B C R) := UnforcedLeray.Algebra.isUnit_one_sub hRt1
  -- the Schur solution w = (I - R̃)⁻¹ a
  have hinv : (1 - schurTilde A B C R) (schurSol A B C R a) = a := by
    unfold schurSol
    calc (1 - schurTilde A B C R) (Ring.inverse (1 - schurTilde A B C R) a)
        = ((1 - schurTilde A B C R) * Ring.inverse (1 - schurTilde A B C R)) a := rfl
      _ = (1 : E →L[ℝ] E) a := by rw [Ring.mul_inverse_cancel _ hu]
      _ = a := rfl
  have hwEq : schurSol A B C R a = a + schurTilde A B C R (schurSol A B C R a) := by
    have h' := hinv
    rw [mrRed_sub_apply, mrRed_one_apply] at h'
    exact sub_eq_iff_eq_add.mp h'
  have hdiff : schurSol A B C R a - a = schurTilde A B C R (schurSol A B C R a) := by
    rw [sub_eq_iff_eq_add, add_comm]
    exact hwEq
  -- norm bound on w
  have hMw : ‖Ring.inverse (1 - schurTilde A B C R)‖ ≤ (1 - (r + h))⁻¹ := by
    refine (UnforcedLeray.Algebra.norm_inverse_one_sub_le honeE hRt1).trans ?_
    exact inv_anti₀ (by linarith) (by linarith)
  have hwn : ‖schurSol A B C R a‖ ≤ (1 - (r + h))⁻¹ * ‖a‖ := by
    unfold schurSol
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right hMw (norm_nonneg _))
  -- Part 2: the deviation bound
  have hell : ℓ (schurSol A B C R a) - ℓ a = ℓ (schurTilde A B C R (schurSol A B C R a)) := by
    rw [← map_sub, hdiff]
  have hbound : |ℓ (schurSol A B C R a) - ℓ a| ≤ ‖ℓ‖ * ‖a‖ * ((r + h) / (1 - (r + h))) := by
    rw [hell, ← Real.norm_eq_abs]
    have hR1 : ‖schurTilde A B C R (schurSol A B C R a)‖
        ≤ (r + h) * ‖schurSol A B C R a‖ :=
      (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right hRt (norm_nonneg _))
    calc ‖ℓ (schurTilde A B C R (schurSol A B C R a))‖
        ≤ ‖ℓ‖ * ‖schurTilde A B C R (schurSol A B C R a)‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖ℓ‖ * ((r + h) * ‖schurSol A B C R a‖) :=
          mul_le_mul_of_nonneg_left hR1 (norm_nonneg _)
      _ ≤ ‖ℓ‖ * ((r + h) * ((1 - (r + h))⁻¹ * ‖a‖)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hwn hq0) (norm_nonneg _)
      _ = ‖ℓ‖ * ‖a‖ * ((r + h) / (1 - (r + h))) := by ring
  -- Part 3: the block solution when ℓ w = 1
  refine ⟨hRt, hbound, fun h1 => ?_⟩
  have hne : schurSol A B C R a ≠ 0 := by
    intro h0
    rw [h0, map_zero] at h1
    norm_num at h1
  have hy : (1 - C) (Ring.inverse (1 - C) (B (schurSol A B C R a)))
      = B (schurSol A B C R a) := by
    calc (1 - C) (Ring.inverse (1 - C) (B (schurSol A B C R a)))
        = ((1 - C) * Ring.inverse (1 - C)) (B (schurSol A B C R a)) := rfl
      _ = (1 : X →L[ℝ] X) (B (schurSol A B C R a)) := by rw [Ring.mul_inverse_cancel _ hCu]
      _ = B (schurSol A B C R a) := rfl
  have hyeq : Ring.inverse (1 - C) (B (schurSol A B C R a))
      = B (schurSol A B C R a) + C (Ring.inverse (1 - C) (B (schurSol A B C R a))) := by
    have h' := hy
    rw [mrRed_sub_apply, mrRed_one_apply] at h'
    exact sub_eq_iff_eq_add.mp h'
  refine ⟨hne, ?_, hyeq⟩
  rw [h1, one_smul, add_assoc, ← mrRed_schurTilde_apply A B C R (schurSol A B C R a)]
  exact hwEq

end UnforcedLeray.Short.PartIIIb
