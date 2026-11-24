import UnforcedLeray.Short.PartIIIa.Sub.T15

/-!
# Part III-a, task `PartIII-a:T15/1`: the elementary Gaussian supremum (SP 3604-3606)

Proves `gaussSup : GaussSup` (`Sub/T15.lean`, SP 3604-3606: substitution `a = |x|^2 r`).
Given `s ≥ 0`, the constant `C = 8^s (s/e)^s` works. The proof uses the substitution
`x = r²/a`, which turns `a^{-s} e^{-r²/(8a)}` into `r^{-2s} · x^s e^{-x/8}`.

1. `u^s e^{-u} ≤ (s/e)^s` for `u, s ≥ 0` (`aux_mul_exp_neg`): from `v ≤ e^{v-1}` with `v = u/s`
   one gets `u ≤ (s/e) e^{u/s}`, and raising to the power `s` gives the bound.
2. `x^s e^{-x/8} ≤ 8^s (s/e)^s` (`aux_div_eight`), using `x = 8 (x/8)`.
3. `a^{-s} e^{-r²/(8a)} = (r²/a)^s e^{-(r²/a)/8} r^{-2s}`, since `(r²)^s r^{-2s} = 1`.
-/

namespace UnforcedLeray.Short.IIIa

/-- Step 1: `u^s e^{-u} ≤ (s/e)^s` for `u, s ≥ 0`. -/
private lemma aux_mul_exp_neg {s u : ℝ} (hs : 0 ≤ s) (hu : 0 ≤ u) :
    u ^ s * Real.exp (-u) ≤ (s / Real.exp 1) ^ s := by
  rcases hs.eq_or_lt with h | h
  · subst h
    simp only [Real.rpow_zero, one_mul]
    rw [Real.exp_le_one_iff]
    linarith
  · have hne : s ≠ 0 := h.ne'
    have hv : u / s ≤ Real.exp (u / s - 1) := by
      have := Real.add_one_le_exp (u / s - 1)
      linarith
    have hexp : Real.exp (u / s - 1) = Real.exp (u / s) / Real.exp 1 := by
      rw [Real.exp_sub]
    have h1 : u ≤ (s / Real.exp 1) * Real.exp (u / s) := by
      have hsu : s * (u / s) = u := by field_simp
      calc u = s * (u / s) := hsu.symm
        _ ≤ s * (Real.exp (u / s) / Real.exp 1) := by
          rw [← hexp]
          exact mul_le_mul_of_nonneg_left hv h.le
        _ = (s / Real.exp 1) * Real.exp (u / s) := by ring
    have h2 : u ^ s ≤ ((s / Real.exp 1) * Real.exp (u / s)) ^ s :=
      Real.rpow_le_rpow hu h1 h.le
    have h3 : ((s / Real.exp 1) * Real.exp (u / s)) ^ s = (s / Real.exp 1) ^ s * Real.exp u := by
      rw [Real.mul_rpow (div_nonneg h.le (Real.exp_pos 1).le) (Real.exp_pos (u / s)).le,
        ← Real.exp_mul]
      rw [show u / s * s = u by field_simp]
    have h4 : u ^ s * Real.exp (-u) ≤ (s / Real.exp 1) ^ s * Real.exp u * Real.exp (-u) :=
      mul_le_mul_of_nonneg_right (h2.trans h3.le) (Real.exp_pos _).le
    have h5 : Real.exp u * Real.exp (-u) = 1 := by
      rw [← Real.exp_add]
      simp
    calc u ^ s * Real.exp (-u) ≤ (s / Real.exp 1) ^ s * Real.exp u * Real.exp (-u) := h4
      _ = (s / Real.exp 1) ^ s * (Real.exp u * Real.exp (-u)) := by ring
      _ = (s / Real.exp 1) ^ s := by rw [h5, mul_one]

/-- Step 2: `x^s e^{-x/8} ≤ 8^s (s/e)^s` for `x, s ≥ 0`. -/
private lemma aux_div_eight {s x : ℝ} (hs : 0 ≤ s) (hx : 0 ≤ x) :
    x ^ s * Real.exp (-x / 8) ≤ 8 ^ s * (s / Real.exp 1) ^ s := by
  have hu : 0 ≤ x / 8 := div_nonneg hx (by norm_num)
  have hA := aux_mul_exp_neg hs hu
  have hx8 : x ^ s = 8 ^ s * (x / 8) ^ s := by
    rw [← Real.mul_rpow (by norm_num : (0:ℝ) ≤ 8) hu, show (8:ℝ) * (x / 8) = x by ring]
  have he : Real.exp (-x / 8) = Real.exp (-(x / 8)) := by
    rw [neg_div]
  rw [hx8, he, mul_assoc]
  exact mul_le_mul_of_nonneg_left hA (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 8) s)

/-- **Elementary Gaussian supremum** (`PartIII-a:T15/1`; SP 3604-3606): for `s ≥ 0` there is
`C ≥ 0` with `a^{-s} e^{-r²/(8a)} ≤ C r^{-2s}` for all `a, r > 0`. -/
theorem gaussSup : UnforcedLeray.Short.IIIa.GaussSup := by
  intro s hs
  refine ⟨8 ^ s * (s / Real.exp 1) ^ s, ?_, ?_⟩
  · exact mul_nonneg (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 8) s)
      (Real.rpow_nonneg (div_nonneg hs (Real.exp_pos 1).le) s)
  · intro a r ha hr
    have hp : 0 < (r ^ 2) ^ s := Real.rpow_pos_of_pos (pow_pos hr 2) s
    have h2 : (r ^ 2) ^ s = r ^ (2 * s) := by
      rw [Real.rpow_mul hr.le, Real.rpow_two]
    have h3 : r ^ (-2 * s) = ((r ^ 2) ^ s)⁻¹ := by
      rw [h2, neg_mul, Real.rpow_neg hr.le]
    have hpow : (r ^ 2) ^ s * r ^ (-2 * s) = 1 := by
      rw [h3]
      exact mul_inv_cancel₀ hp.ne'
    have e1 : -r ^ 2 / (8 * a) = -(r ^ 2 / a) / 8 := by
      ring
    have hid : a ^ (-s) * Real.exp (-r ^ 2 / (8 * a))
        = (r ^ 2 / a) ^ s * Real.exp (-(r ^ 2 / a) / 8) * r ^ (-2 * s) := by
      rw [e1, Real.div_rpow (sq_nonneg r) ha.le, Real.rpow_neg ha.le]
      linear_combination (-((a ^ s)⁻¹ * Real.exp (-(r ^ 2 / a) / 8))) * hpow
    have K : (r ^ 2 / a) ^ s * Real.exp (-(r ^ 2 / a) / 8) ≤ 8 ^ s * (s / Real.exp 1) ^ s :=
      aux_div_eight hs (div_nonneg (sq_nonneg r) ha.le)
    rw [hid]
    exact mul_le_mul_of_nonneg_right K (Real.rpow_nonneg hr.le _)

end UnforcedLeray.Short.IIIa
