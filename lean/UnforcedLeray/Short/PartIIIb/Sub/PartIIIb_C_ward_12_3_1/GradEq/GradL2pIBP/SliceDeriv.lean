import Mathlib.Analysis.InnerProductSpace.NormPow

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete.GradSlice

open Real

/-- Derivative of `y ↦ ‖y‖ ^ s • y` in a real inner product space. -/
theorem fderiv_normPow_smul {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x v : E) {s : ℝ} (hs : 1 < s) :
    fderiv ℝ (fun y : E => ‖y‖ ^ s • y) x v
      = ‖x‖ ^ s • v + (s * ‖x‖ ^ (s - 2) * inner ℝ x v) • x := by
  have h : HasFDerivAt (fun y : E => ‖y‖ ^ s • y)
      (‖x‖ ^ s • ContinuousLinearMap.id ℝ E
        + ((s * ‖x‖ ^ (s - 2)) • innerSL ℝ x).smulRight x) x :=
    (hasFDerivAt_norm_rpow x hs).smul (hasFDerivAt_id x)
  rw [h.fderiv]
  simp [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]

/-- Norm bound on the derivative of `y ↦ ‖y‖ ^ s • y`. -/
theorem norm_fderiv_normPow_smul_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x v : E) {s : ℝ} (hs : 1 < s) :
    ‖fderiv ℝ (fun y : E => ‖y‖ ^ s • y) x v‖ ≤ (s + 1) * ‖x‖ ^ s * ‖v‖ := by
  rw [fderiv_normPow_smul x v hs]
  have e1 : ‖x‖ ^ (s - 1) = ‖x‖ ^ (s - 2) * ‖x‖ := by
    rw [← Real.rpow_add_one' (norm_nonneg x) (by linarith)]; ring_nf
  have e2 : ‖x‖ ^ s = ‖x‖ ^ (s - 1) * ‖x‖ := by
    rw [← Real.rpow_add_one' (norm_nonneg x) (by linarith)]; ring_nf
  have hxs : 0 ≤ ‖x‖ ^ s := Real.rpow_nonneg (norm_nonneg x) s
  have hx2 : 0 ≤ ‖x‖ ^ (s - 2) := Real.rpow_nonneg (norm_nonneg x) (s - 2)
  have hi : |inner ℝ x v| ≤ ‖x‖ * ‖v‖ := abs_real_inner_le_norm x v
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hxs,
    abs_mul, abs_mul, abs_of_nonneg hx2, abs_of_nonneg (by linarith : (0:ℝ) ≤ s)]
  have hs1 : |inner ℝ x v| * ‖x‖ ≤ ‖x‖ * ‖v‖ * ‖x‖ := by
    exact mul_le_mul_of_nonneg_right hi (norm_nonneg x)
  have key : s * (‖x‖ ^ (s - 2) * |inner ℝ x v|) * ‖x‖ ≤ s * ‖x‖ ^ s * ‖v‖ := by
    have : s * (‖x‖ ^ (s - 2) * |inner ℝ x v|) * ‖x‖ = s * ‖x‖ ^ (s - 2) * (|inner ℝ x v| * ‖x‖) := by ring
    rw [this]
    have hsn : 0 ≤ s * ‖x‖ ^ (s - 2) := by positivity
    calc s * ‖x‖ ^ (s - 2) * (|inner ℝ x v| * ‖x‖) ≤ s * ‖x‖ ^ (s - 2) * (‖x‖ * ‖v‖ * ‖x‖) :=
          mul_le_mul_of_nonneg_left hs1 hsn
      _ = s * (‖x‖ ^ (s - 1) * ‖x‖) * ‖v‖ := by rw [e1]; ring
      _ = s * ‖x‖ ^ s * ‖v‖ := by rw [e2]
  have hfin : ‖x‖ ^ s * ‖v‖ + s * (‖x‖ ^ (s - 2) * |inner ℝ x v|) * ‖x‖
      ≤ (s + 1) * ‖x‖ ^ s * ‖v‖ := by
    nlinarith [key, mul_nonneg hxs (norm_nonneg v)]
  linarith [hfin]

end UnforcedLeray.Short.PartIIIb.Concrete.GradSlice
