import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

/-!
# Pointwise upper bound for the Gaussian spectral potential

This proves the scalar inequality in `paper/main.tex`, lines 1010--1035.
The value at the removable singularity is specified explicitly. The theorem
is pointwise: it does not assert a strict bound for the supremum without a
separate compactness/attainment argument.
-/

noncomputable section
namespace UnforcedLeray.GaussianPotential

/-- The difference between nine times the denominator and the numerator. -/
def F9 (y : ℝ) : ℝ := 9 * (Real.exp y - 1) - 8 * y - 4 * y ^ 2

/-- The manuscript's potential, with its continuous-extension value at zero. -/
def W (y : ℝ) : ℝ := if y = 0 then 8 else 4 * (y + 2) * y / (Real.exp y - 1)

@[simp] theorem F9_zero : F9 0 = 0 := by simp [F9]
@[simp] theorem W_zero : W 0 = 8 := by simp [W]

/-- Explicit derivative of the comparison function. -/
theorem hasDerivAt_F9 (y : ℝ) :
    HasDerivAt F9 (9 * Real.exp y - 8 - 8 * y) y := by
  have h1 : HasDerivAt (fun x : ℝ => 9 * (Real.exp x - 1))
      (9 * Real.exp y) y := by
    simpa using ((Real.hasDerivAt_exp y).sub_const 1).const_mul 9
  have h2 : HasDerivAt (fun x : ℝ => 8 * x) 8 y := by
    simpa using (hasDerivAt_id y).const_mul 8
  have h3 : HasDerivAt (fun x : ℝ => 4 * x ^ 2) (8 * y) y := by
    convert (hasDerivAt_pow 2 y).const_mul 4 using 1 <;> norm_num <;> first | rfl | ring
  exact (h1.sub h2).sub h3

/-- Strict positivity follows already from `exp y ≥ 1+y` and `exp y > 0`. -/
theorem F9_derivative_pos (y : ℝ) : 0 < 9 * Real.exp y - 8 - 8 * y := by
  have h := Real.add_one_le_exp y
  have hp := Real.exp_pos y
  linarith

theorem F9_strictMono : StrictMono F9 :=
  strictMono_of_hasDerivAt_pos hasDerivAt_F9 F9_derivative_pos

theorem F9_pos {y : ℝ} (hy : 0 < y) : 0 < F9 y := by
  simpa using F9_strictMono hy

theorem F9_neg {y : ℝ} (hy : y < 0) : F9 y < 0 := by
  simpa using F9_strictMono hy

/-- The genuine scalar estimate, including both signs of the denominator. -/
theorem W_lt_nine (y : ℝ) : W y < 9 := by
  by_cases hy : y = 0
  · norm_num [hy]
  · simp only [W, hy, ↓reduceIte]
    rcases lt_or_gt_of_ne hy with hneg | hpos
    · have hd : Real.exp y - 1 < 0 := sub_neg.mpr (Real.exp_lt_one_iff.mpr hneg)
      apply (div_lt_iff_of_neg hd).2
      have hf := F9_neg hneg
      unfold F9 at hf
      nlinarith
    · have hd : 0 < Real.exp y - 1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr hpos)
      apply (div_lt_iff₀ hd).2
      have hf := F9_pos hpos
      unfold F9 at hf
      nlinarith

/-- In particular, the estimate holds on the manuscript's radial domain. -/
theorem W_lt_nine_on_radial_domain {y : ℝ} (_hy : -2 < y) : W y < 9 := W_lt_nine y

end UnforcedLeray.GaussianPotential
