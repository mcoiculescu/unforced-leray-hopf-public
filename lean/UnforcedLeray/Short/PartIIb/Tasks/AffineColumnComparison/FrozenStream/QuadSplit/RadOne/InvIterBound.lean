import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_2_2_4_1

/-!
# Part II-b, task `PartII-b:G4/2/2/4/1/2`: `InvIterBound`

Source of record: `the November 2 reference manuscript`, lines 2349-2352.

Route: for `t > 0`, `d^i (s⁻¹) = c_i t^{-(i+1)}` with `c_i` real (induction on `i`, complex
values through `HasDerivAt.ofReal_comp`). For `t ≥ 1` the exponent is `≤ -1 < 0`, so the factor
`t^{-(i+1)}` lies in `(0, 1]`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

/-- Derivatives of `s ↦ s⁻¹` on `(0,∞)` are real constant multiples of powers of `t`. -/
theorem inv_iteratedDeriv_form (i : ℕ) :
    ∃ c : ℝ, ∀ t : ℝ, 0 < t →
      iteratedDeriv i (fun s : ℝ => ((s⁻¹ : ℝ) : ℂ)) t =
        (((c * t ^ (-((i : ℝ) + 1))) : ℝ) : ℂ) := by
  induction i with
  | zero =>
    refine ⟨1, fun t _ => ?_⟩
    simp [Real.rpow_neg_one]
  | succ n ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨c * (-((n : ℝ) + 1)), fun t ht => ?_⟩
    have hev : iteratedDeriv n (fun s : ℝ => ((s⁻¹ : ℝ) : ℂ)) =ᶠ[𝓝 t]
        fun s : ℝ => (((c * s ^ (-((n : ℝ) + 1))) : ℝ) : ℂ) := by
      filter_upwards [Ioi_mem_nhds ht] with s hs
      exact hc s hs
    have hd : HasDerivAt (fun s : ℝ => (((c * s ^ (-((n : ℝ) + 1))) : ℝ) : ℂ))
        ((((c * ((-((n : ℝ) + 1)) * t ^ (-((n : ℝ) + 1) - 1))) : ℝ)) : ℂ) t := by
      have h1 : HasDerivAt (fun s : ℝ => c * s ^ (-((n : ℝ) + 1)))
          (c * ((-((n : ℝ) + 1)) * t ^ (-((n : ℝ) + 1) - 1))) t :=
        (Real.hasDerivAt_rpow_const (Or.inl ht.ne')).const_mul c
      exact h1.ofReal_comp
    rw [iteratedDeriv_succ, hev.deriv_eq, hd.deriv]
    have hexp : -((n : ℝ) + 1) - 1 = -(((n + 1 : ℕ) : ℝ) + 1) := by
      push_cast
      ring
    rw [hexp]
    congr 1
    ring

theorem invIterBound : UnforcedLeray.Short.IIb.InvIterBound := by
  intro i
  obtain ⟨c, hc⟩ := inv_iteratedDeriv_form i
  refine ⟨|c|, fun t ht => ?_⟩
  have ht0 : 0 < t := by linarith
  have hnonpos : -((i : ℝ) + 1) ≤ 0 := by
    have : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
    linarith
  have hp : t ^ (-((i : ℝ) + 1)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos ht hnonpos
  have hpos : 0 ≤ t ^ (-((i : ℝ) + 1)) :=
    Real.rpow_nonneg ht0.le _
  rw [hc t ht0, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg hpos]
  exact mul_le_of_le_one_right (abs_nonneg c) hp

end
