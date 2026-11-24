import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Sub1

/-!
# `KF5b`: the substitution `l = e^{-t/2}` (source 3616, 3620-3626)

The map `l ↦ -2 log l` is a decreasing diffeomorphism `(0,1) → (0,∞)` with derivative `-2/l`.
Mathlib's `integral_image_eq_integral_abs_deriv_smul` gives the change of variables without
integrability hypotheses. On `(0,1)`, `e^{-μt} = l^{2μ}` at `t = -2 log l`, `e^{-t/2} = l`,
`τ - t = τ + 2 log l`, and `|-2/l| = 2/l`, so the integrand becomes `2 R l^{2μ+2} S`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization

theorem kf5b_image : (fun l : ℝ => -2 * Real.log l) '' Ioo (0 : ℝ) 1 = Ioi (0 : ℝ) := by
  ext t
  constructor
  · rintro ⟨l, ⟨hl0, hl1⟩, rfl⟩
    have := Real.log_neg hl0 hl1
    simp only [mem_Ioi]
    linarith
  · intro ht
    refine ⟨Real.exp (-t / 2), ⟨Real.exp_pos _, ?_⟩, ?_⟩
    · rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr (by simp only [mem_Ioi] at ht; linarith)
    · simp only
      rw [Real.log_exp]
      ring

theorem kf5b_injOn : InjOn (fun l : ℝ => -2 * Real.log l) (Ioo (0 : ℝ) 1) := by
  intro a ha b hb hab
  simp only at hab
  have hlog : Real.log a = Real.log b := by linarith
  exact Real.log_injOn_pos (Ioo_subset_Ioi_self ha) (Ioo_subset_Ioi_self hb) hlog

theorem kf5b_deriv : ∀ l ∈ Ioo (0 : ℝ) 1,
    HasDerivWithinAt (fun l : ℝ => -2 * Real.log l) (-2 * l⁻¹) (Ioo (0 : ℝ) 1) l := by
  intro l hl
  exact ((Real.hasDerivAt_log hl.1.ne').const_mul (-2)).hasDerivWithinAt

/-- **KF5b** (3616, `-2dλ/λ`): the change of variables `l = e^{-t/2}` from `(0,∞)` to `(0,1)`. -/
theorem kf5b : KF5b := by
  unfold KF5b
  intro ν μ R T y τ i
  rw [← kf5b_image, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo kf5b_deriv
    kf5b_injOn, ← integral_const_mul, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioo (fun l hl => ?_)
  have hl0 : (0 : ℝ) < l := hl.1
  have e1 : Real.exp (-(-2 * Real.log l) / 2) = l := by
    rw [show -(-2 * Real.log l) / 2 = Real.log l by ring]
    exact Real.exp_log hl0
  have e2 : τ - (-2 * Real.log l) = τ + 2 * Real.log l := by ring
  have ea : |(-2 : ℝ) * l⁻¹| = 2 * l⁻¹ := by
    have hneg : (-2 : ℝ) * l⁻¹ < 0 := by
      have := inv_pos.mpr hl0
      linarith
    rw [abs_of_neg hneg]
    ring
  have hl0c : (l : ℂ) ≠ 0 := by exact_mod_cast hl0.ne'
  have hexp : Complex.exp (-μ * ((-2 * Real.log l : ℝ) : ℂ)) = (l : ℂ) ^ (2 * μ) := by
    rw [Complex.cpow_def_of_ne_zero hl0c, ← Complex.ofReal_log hl0.le]
    congr 1
    push_cast
    ring
  have hpow : (l : ℂ) ^ (2 * μ + 2) = (l : ℂ) ^ (2 * μ) * (l : ℂ) ^ (2 : ℕ) := by
    rw [Complex.cpow_add _ _ hl0c, Complex.cpow_two]
  rw [e1, e2, ea, hexp, hpow, Complex.real_smul]
  push_cast
  field_simp

end UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization
