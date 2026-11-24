import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_14_2_3_1

/-!
# Axisymmetry of the lifted tensor norm (`PartIII-b:C/near/masked/14/2/3/1/1`)

Source: `the November 2 reference manuscript`
2666-2668, 2683, 3996-4011.  `liftNorm R c f τ z` depends on `z` only through `(z₀²+z₁², z₂)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal Matrix

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Short.PartIIIb.NearInst.Delta
  UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Blueprint.Planar

/-- Frobenius norm as a trace. -/
lemma la_tensorNorm_eq (A : Matrix (Fin 3) (Fin 3) ℝ) :
    UnforcedLeray.Short.IIIa.tensorNorm A = Real.sqrt (Matrix.trace (Aᵀ * A)) := by
  unfold UnforcedLeray.Short.IIIa.tensorNorm
  congr 1
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply,
    Fin.sum_univ_three]
  ring

/-- Orthogonal invariance of the Frobenius norm under `N ↦ Q N Qᵀ`. -/
lemma la_tensorNorm_orth (Q N : Matrix (Fin 3) (Fin 3) ℝ) (hQ : Qᵀ * Q = 1) :
    UnforcedLeray.Short.IIIa.tensorNorm (Q * N * Qᵀ) = UnforcedLeray.Short.IIIa.tensorNorm N := by
  rw [la_tensorNorm_eq, la_tensorNorm_eq]
  congr 1
  have h1 : (Q * N * Qᵀ)ᵀ * (Q * N * Qᵀ) = Q * (Nᵀ * (Qᵀ * Q) * N) * Qᵀ := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  rw [h1, hQ, Matrix.mul_one, Matrix.trace_mul_cycle, hQ, Matrix.one_mul]

/-- The cylindrical frame is orthogonal away from the axis. -/
lemma la_cylFrame_orth (z : Space) (h : hRad z ≠ 0) : (cylFrame z)ᵀ * cylFrame z = 1 := by
  have hsq : hRad z ^ 2 = z 0 ^ 2 + z 1 ^ 2 := Real.sq_sqrt (by positivity)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cylFrame, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply] <;>
    field_simp <;>
    nlinarith [hsq]

theorem liftAxisym : UnforcedLeray.Short.PartIIIb.NearInst.Masked.LiftAxisym := by
  intro R c f τ z z' hxy hz
  have hR : hRad z = hRad z' := by unfold hRad; rw [hxy]
  have hp : chartOf R c z' τ = chartOf R c z τ := by
    unfold chartOf; rw [hR, hz]
  by_cases h0 : hRad z = 0
  · have hs : z 0 ^ 2 + z 1 ^ 2 = 0 := by
      unfold hRad at h0
      have := Real.sqrt_eq_zero'.mp h0
      nlinarith [sq_nonneg (z 0), sq_nonneg (z 1)]
    have hs' : z' 0 ^ 2 + z' 1 ^ 2 = 0 := by rw [← hxy, hs]
    have a0 : z 0 = 0 := by
      have : z 0 ^ 2 = 0 := by nlinarith [sq_nonneg (z 0), sq_nonneg (z 1)]
      simpa using this
    have a1 : z 1 = 0 := by
      have : z 1 ^ 2 = 0 := by nlinarith [sq_nonneg (z 0), sq_nonneg (z 1)]
      simpa using this
    have b0 : z' 0 = 0 := by
      have : z' 0 ^ 2 = 0 := by nlinarith [sq_nonneg (z' 0), sq_nonneg (z' 1)]
      simpa using this
    have b1 : z' 1 = 0 := by
      have : z' 1 ^ 2 = 0 := by nlinarith [sq_nonneg (z' 0), sq_nonneg (z' 1)]
      simpa using this
    have hcyl : cylFrame z' = cylFrame z := by
      simp [cylFrame, a0, a1, b0, b1]
    unfold liftNorm cartLift
    rw [hp, hcyl]
  · have h0' : hRad z' ≠ 0 := by rw [← hR]; exact h0
    have e1 : liftNorm R c f τ z = UnforcedLeray.Short.IIIa.tensorNorm
        ((chartOf R c z τ).1 • nsSym (f (chartOf R c z τ))) := by
      unfold liftNorm cartLift
      exact la_tensorNorm_orth _ _ (la_cylFrame_orth z h0)
    have e2 : liftNorm R c f τ z' = UnforcedLeray.Short.IIIa.tensorNorm
        ((chartOf R c z τ).1 • nsSym (f (chartOf R c z τ))) := by
      unfold liftNorm cartLift
      rw [hp]
      exact la_tensorNorm_orth _ _ (la_cylFrame_orth z' h0')
    rw [e1, e2]

end UnforcedLeray.Short.PartIIIb.NearInst.Masked
