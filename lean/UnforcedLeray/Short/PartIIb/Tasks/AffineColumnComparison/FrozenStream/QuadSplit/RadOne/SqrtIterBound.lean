import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_2_2_4_1

/-!
# Part II-b, task `PartII-b:G4/2/2/4/1/1`: `SqrtIterBound`

Source of record: `the November 2 reference manuscript`, lines 2349-2352.

Route: for `t > 0`, `d^i √t = c_i t^{1/2 - i}` (induction on `i`), and for `t ≥ 1` and `i ≥ 1`
the exponent is `≤ 0`, so the factor `t^{1/2-(i+1)}` lies in `(0, 1]`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

/-- Derivatives of `√` on `(0,∞)` are constant multiples of powers of `t`. -/
theorem sqrt_iteratedDeriv_form (i : ℕ) :
    ∃ c : ℝ, ∀ t : ℝ, 0 < t →
      iteratedDeriv i Real.sqrt t = c * t ^ (1 / 2 - (i : ℝ)) := by
  induction i with
  | zero =>
    refine ⟨1, fun t _ => ?_⟩
    simp [Real.sqrt_eq_rpow]
  | succ n ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨c * (1 / 2 - (n : ℝ)), fun t ht => ?_⟩
    have hev : iteratedDeriv n Real.sqrt =ᶠ[𝓝 t] fun s : ℝ => c * s ^ (1 / 2 - (n : ℝ)) := by
      filter_upwards [Ioi_mem_nhds ht] with s hs
      exact hc s hs
    rw [iteratedDeriv_succ, hev.deriv_eq, deriv_const_mul_field, Real.deriv_rpow_const]
    have hexp : (1 / 2 : ℝ) - ((n + 1 : ℕ) : ℝ) = (1 / 2 - (n : ℝ)) - 1 := by
      push_cast
      ring
    rw [hexp]
    ring

theorem sqrtIterBound : UnforcedLeray.Short.IIb.SqrtIterBound := by
  intro i
  obtain ⟨c, hc⟩ := sqrt_iteratedDeriv_form (i + 1)
  refine ⟨|c|, fun t ht => ?_⟩
  have ht0 : 0 < t := by linarith
  have hnonpos : (1 / 2 : ℝ) - ((i + 1 : ℕ) : ℝ) ≤ 0 := by
    have : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
    push_cast
    linarith
  have hp : t ^ ((1 / 2 : ℝ) - ((i + 1 : ℕ) : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos ht hnonpos
  have hpos : 0 ≤ t ^ ((1 / 2 : ℝ) - ((i + 1 : ℕ) : ℝ)) :=
    Real.rpow_nonneg ht0.le _
  rw [hc t ht0, Real.norm_eq_abs, abs_mul, abs_of_nonneg hpos]
  exact mul_le_of_le_one_right (abs_nonneg c) hp

end
