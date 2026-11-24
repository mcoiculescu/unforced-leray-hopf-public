import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Std.Tactic.BVDecide.LRAT.Internal.Formula.RupAddResult

/-!
# Part II-b, task `PartII-b:G4/2/3/4/5`: the bound on `csc²`

Source of record: `the November 2 reference manuscript`, lines 2349-2358.

For `w = a + i b` one has `|sin w|² = sin²a cosh²b + cos²a sinh²b ≥ sinh²b`, hence
`|sin w|⁻² ≤ 4 e^{-2|b|}/(1 - e^{-2|b|})²`.
-/

set_option autoImplicit false

noncomputable section

open Complex

namespace UnforcedLeray.Short.IIb

/-- `|sin (a + i b)| ≥ |sinh b|` for real `a`, `b`. -/
lemma csc_norm_ge_sinh (a b : ℝ) :
    |Real.sinh b| ≤ ‖Complex.sin ((a : ℂ) + (b : ℂ) * Complex.I)‖ := by
  have key : Complex.sin ((a : ℂ) + (b : ℂ) * Complex.I)
      = ((Real.sin a * Real.cosh b : ℝ) : ℂ) + ((Real.cos a * Real.sinh b : ℝ) : ℂ) * Complex.I := by
    rw [Complex.sin_add_mul_I]
    push_cast
    ring
  rw [key]
  have hn : ‖((Real.sin a * Real.cosh b : ℝ) : ℂ) + ((Real.cos a * Real.sinh b : ℝ) : ℂ) * Complex.I‖ ^ 2
      = (Real.sin a * Real.cosh b) ^ 2 + (Real.cos a * Real.sinh b) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_add_mul_I]
  have hA : (Real.sin a * Real.cosh b) ^ 2 + (Real.cos a * Real.sinh b) ^ 2
      = Real.sin a ^ 2 + Real.sinh b ^ 2 := by
    linear_combination (Real.sin a) ^ 2 * Real.cosh_sq' (x := b) + Real.sinh b ^ 2 * Real.sin_sq_add_cos_sq a
  have hsq : |Real.sinh b| ^ 2 ≤ ‖((Real.sin a * Real.cosh b : ℝ) : ℂ) + ((Real.cos a * Real.sinh b : ℝ) : ℂ) * Complex.I‖ ^ 2 := by
    rw [hn, hA, sq_abs]
    nlinarith [sq_nonneg (Real.sin a)]
  exact (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).1 hsq

/-- **`csc_sq_bound`** (SP 2349-2358): the reciprocal of `|sin|²` at `π z / c` with `Im z ≠ 0`. -/
theorem csc_sq_bound (c : ℝ) (hc : 0 < c) (z : ℂ) (hz : z.im ≠ 0) :
    ‖((Real.pi : ℂ) / c) ^ 2 / Complex.sin (Real.pi * z / c) ^ 2‖
      ≤ 4 * (Real.pi / c) ^ 2 * Real.exp (-(2 * Real.pi * |z.im| / c))
        / (1 - Real.exp (-(2 * Real.pi * |z.im| / c))) ^ 2 := by
  set q : ℝ := Real.pi / c with hq
  have hqpos : 0 < q := div_pos Real.pi_pos hc
  set w : ℂ := ((q : ℝ) : ℂ) * z with hwdef
  have e1 : (Real.pi : ℂ) * z / (c : ℂ) = w := by
    rw [hwdef, hq]
    push_cast
    ring
  have e2 : (Real.pi : ℂ) * z / (c : ℂ) = (w.re : ℂ) + (w.im : ℂ) * Complex.I := by
    rw [Complex.re_add_im]
    exact e1
  have hS : |Real.sinh w.im| ≤ ‖Complex.sin (Real.pi * z / c)‖ := by
    rw [e2]
    exact csc_norm_ge_sinh _ _
  have hwim : w.im = q * z.im := by
    rw [hwdef, Complex.im_ofReal_mul]
  have hpc : ‖(Real.pi : ℂ) / (c : ℂ)‖ = q := by
    rw [← Complex.ofReal_div, Complex.norm_real, Real.norm_of_nonneg hqpos.le]
  -- the sinh argument, with the absolute value of `Im z`
  set u : ℝ := |z.im| with hu
  have hupos : 0 < u := abs_pos.mpr hz
  have hsq : Real.sinh (q * z.im) ^ 2 = Real.sinh (q * u) ^ 2 := by
    rcases abs_choice z.im with h | h <;> simp [hu, h, mul_neg, Real.sinh_neg]
  set T : ℝ := q * u with hT
  have hTpos : 0 < T := mul_pos hqpos hupos
  have hE : Real.exp (-(2 * Real.pi * u / c)) = Real.exp (-(2 * T)) := by
    congr 1
    rw [hT, hq]
    ring
  rw [hE]
  set p : ℝ := Real.exp T with hp
  have hp1 : 1 < p := Real.one_lt_exp_iff.mpr hTpos
  have hp0 : 0 < p := by linarith
  have hE2 : Real.exp (-(2 * T)) = (p * p)⁻¹ := by
    rw [show -(2 * T) = -(T + T) by ring, Real.exp_neg, Real.exp_add]
  rw [hE2]
  set E : ℝ := (p * p)⁻¹ with hEdef
  have hE0 : 0 < E := by positivity
  have hE1 : E < 1 := by
    rw [hEdef]
    apply inv_lt_one_of_one_lt₀
    nlinarith
  -- the identity `sinh² T · 4E = (1 - E)²`
  have hid : Real.sinh T ^ 2 * (4 * E) = (1 - E) ^ 2 := by
    rw [Real.sinh_eq, Real.exp_neg, ← hp, hEdef]
    field_simp
    ring
  have hsinhpos : 0 < Real.sinh T ^ 2 := by
    have : 0 < Real.sinh T := Real.sinh_pos_iff.mpr hTpos
    positivity
  -- lower bound on the modulus
  have hden : 0 < Real.sinh T ^ 2 := hsinhpos
  have hlow : Real.sinh T ^ 2 ≤ ‖Complex.sin (Real.pi * z / c)‖ ^ 2 := by
    have h1 : Real.sinh T ^ 2 = Real.sinh (w.im) ^ 2 := by
      rw [hwim, hsq]
    have h2 : Real.sinh (w.im) ^ 2 = |Real.sinh w.im| ^ 2 := (sq_abs _).symm
    rw [h1, h2]
    exact pow_le_pow_left₀ (abs_nonneg _) hS 2
  have hnorm_pos : 0 < ‖Complex.sin (Real.pi * z / c)‖ ^ 2 := lt_of_lt_of_le hsinhpos hlow
  rw [norm_div, norm_pow, norm_pow, hpc]
  have hmain : q ^ 2 / ‖Complex.sin (Real.pi * z / c)‖ ^ 2 ≤ q ^ 2 / Real.sinh T ^ 2 :=
    div_le_div_of_nonneg_left (sq_nonneg q) hsinhpos hlow
  have hkey : q ^ 2 / Real.sinh T ^ 2 = 4 * q ^ 2 * E / (1 - E) ^ 2 := by
    have h1E : (1 - E) ^ 2 ≠ 0 := by
      have : 0 < 1 - E := by linarith
      positivity
    rw [div_eq_div_iff hsinhpos.ne' h1E]
    linear_combination (-(q ^ 2)) * hid
  calc q ^ 2 / ‖Complex.sin (Real.pi * z / c)‖ ^ 2 ≤ q ^ 2 / Real.sinh T ^ 2 := hmain
    _ = 4 * q ^ 2 * E / (1 - E) ^ 2 := hkey

end UnforcedLeray.Short.IIb
