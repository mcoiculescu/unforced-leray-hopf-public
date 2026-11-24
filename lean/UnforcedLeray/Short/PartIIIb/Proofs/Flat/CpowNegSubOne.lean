import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Proof of `cpowNegSubOne` (source: `the November 2 reference manuscript`, lines 4648, 4655-4658)

The factor `(1+νt)^{-κ}` of `F_+(t,0)^{-1}` is `1 + O(νt)` for `0 ≤ νt ≤ 1.1`; here `x = 1+νt`.
Write `x^{-κ} = exp (w)` with `w = log x * (-κ)`, `‖w‖ = log x * ‖κ‖ ≤ (x-1) ‖κ‖ ≤ 1.1 ‖κ‖`,
and use `‖exp w - 1‖ ≤ ‖w‖ exp ‖w‖`.
-/

namespace UnforcedLeray.Short.PartIIIb.ConcreteYF

open Filter Topology Set

theorem cpowNegSubOne (κ : ℂ) (x : ℝ) (hx1 : 1 ≤ x) (hx2 : x ≤ 2.1) : ‖((x : ℂ) ^ (-κ)) - 1‖ ≤ ‖κ‖ * Real.exp (1.1 * ‖κ‖) * (x - 1) := by
  have hx0 : 0 < x := by linarith
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hx0.ne'
  have hL0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hLle : Real.log x ≤ x - 1 := Real.log_le_sub_one_of_pos hx0
  have hxm : x - 1 ≤ 1.1 := by norm_num at hx2 ⊢; linarith
  have hlogC : Complex.log (x : ℂ) = ((Real.log x : ℝ) : ℂ) := by
    rw [Complex.ofReal_log hx0.le]
  have hpow : (x : ℂ) ^ (-κ) = Complex.exp (((Real.log x : ℝ) : ℂ) * (-κ)) := by
    rw [Complex.cpow_def_of_ne_zero hxC, hlogC]
  have hwnorm : ‖((Real.log x : ℝ) : ℂ) * (-κ)‖ = Real.log x * ‖κ‖ := by
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hL0]
  have hexp : ‖Complex.exp (((Real.log x : ℝ) : ℂ) * (-κ)) - 1‖
      ≤ ‖((Real.log x : ℝ) : ℂ) * (-κ)‖ * Real.exp ‖((Real.log x : ℝ) : ℂ) * (-κ)‖ := by
    have h := Complex.norm_exp_sub_sum_le_norm_mul_exp (((Real.log x : ℝ) : ℂ) * (-κ)) 1
    simpa using h
  have hκ : 0 ≤ ‖κ‖ := norm_nonneg κ
  have hwle : ‖((Real.log x : ℝ) : ℂ) * (-κ)‖ ≤ ‖κ‖ * (x - 1) := by
    rw [hwnorm]; nlinarith
  have hwle2 : ‖((Real.log x : ℝ) : ℂ) * (-κ)‖ ≤ 1.1 * ‖κ‖ := by
    rw [hwnorm]; nlinarith
  have hexple : Real.exp ‖((Real.log x : ℝ) : ℂ) * (-κ)‖ ≤ Real.exp (1.1 * ‖κ‖) :=
    Real.exp_le_exp.2 hwle2
  rw [hpow]
  calc ‖Complex.exp (((Real.log x : ℝ) : ℂ) * (-κ)) - 1‖
      ≤ ‖((Real.log x : ℝ) : ℂ) * (-κ)‖ * Real.exp ‖((Real.log x : ℝ) : ℂ) * (-κ)‖ := hexp
    _ ≤ (‖κ‖ * (x - 1)) * Real.exp (1.1 * ‖κ‖) :=
        mul_le_mul hwle hexple (Real.exp_pos _).le (by positivity)
    _ = ‖κ‖ * Real.exp (1.1 * ‖κ‖) * (x - 1) := by ring

end UnforcedLeray.Short.PartIIIb.ConcreteYF
