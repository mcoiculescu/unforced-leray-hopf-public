import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_6
import Mathlib.Analysis.Complex.Exponential

/-!
# Part III-a, `PartIII-a:T21/2/6/12`: absorption of fixed powers into the Gaussian

Source of record: `the November 2 reference manuscript`, lines 2869-2871.
Statement: `ExpPolyAbsorb` (`x^N e^{-βx} ≤ N!/β^N` for `β > 0`, `x ≥ 0`), proved from
`Real.pow_div_factorial_le_exp`: `(βx)^N / N! ≤ e^{βx}`.
-/

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

theorem expPolyAbsorb : ExpPolyAbsorb := by
  intro N β x hβ hx
  have ht : 0 ≤ β * x := mul_nonneg hβ.le hx
  have h1 : (β * x) ^ N / (N.factorial : ℝ) ≤ Real.exp (β * x) :=
    Real.pow_div_factorial_le_exp (β * x) ht N
  have hfac : (0 : ℝ) < (N.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos N
  have h2 : (β * x) ^ N ≤ (N.factorial : ℝ) * Real.exp (β * x) := by
    have h3 := (div_le_iff₀ hfac).mp h1
    linarith [mul_comm (Real.exp (β * x)) (N.factorial : ℝ)]
  have hx' : x ^ N = (β * x) ^ N / β ^ N := by
    rw [mul_pow, mul_div_cancel_left₀ _ (pow_ne_zero N hβ.ne')]
  have hβN : (0 : ℝ) < β ^ N := pow_pos hβ N
  calc x ^ N * Real.exp (-(β * x))
      = (β * x) ^ N * Real.exp (-(β * x)) / β ^ N := by rw [hx']; ring
    _ ≤ ((N.factorial : ℝ) * Real.exp (β * x)) * Real.exp (-(β * x)) / β ^ N := by
        gcongr
    _ = (N.factorial : ℝ) / β ^ N := by
        rw [show ((N.factorial : ℝ) * Real.exp (β * x)) * Real.exp (-(β * x))
            = (N.factorial : ℝ) * (Real.exp (β * x) * Real.exp (-(β * x))) by ring,
          ← Real.exp_add]
        simp

end UnforcedLeray.Short.IIIa
