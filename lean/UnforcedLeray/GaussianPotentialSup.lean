import UnforcedLeray.GaussianPotential
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Exact maximum of the scalar Gaussian potential

A stronger version of the manuscript's `W_max < 9`: the concrete function W
satisfies W(y) ≤ 8 for every real y and attains 8 at y = 0. Thus its actual
supremum is 8. This proves a uniform strict upper bound below 9 without
mistaking a pointwise strict inequality for a strict supremum inequality.
The manuscript is unchanged.
-/

noncomputable section
open Set
namespace UnforcedLeray.GaussianPotential

/-- Comparison with eight times the denominator. -/
def F8 (y : ℝ) : ℝ := 8 * (Real.exp y - 1) - 8 * y - 4 * y ^ 2

@[simp] theorem F8_zero : F8 0 = 0 := by simp [F8]

theorem hasDerivAt_F8 (y : ℝ) :
    HasDerivAt F8 (8 * Real.exp y - 8 - 8 * y) y := by
  have h1 : HasDerivAt (fun x : ℝ => 8 * (Real.exp x - 1))
      (8 * Real.exp y) y := by
    simpa using ((Real.hasDerivAt_exp y).sub_const 1).const_mul 8
  have h2 : HasDerivAt (fun x : ℝ => 8 * x) 8 y := by
    simpa using (hasDerivAt_id y).const_mul 8
  have h3 : HasDerivAt (fun x : ℝ => 4 * x ^ 2) (8 * y) y := by
    convert (hasDerivAt_pow 2 y).const_mul 4 using 1 <;> norm_num <;> first | rfl | ring
  exact (h1.sub h2).sub h3

theorem F8_monotone : Monotone F8 := by
  apply monotone_of_hasDerivAt_nonneg hasDerivAt_F8
  intro y
  change (0 : ℝ) ≤ 8 * Real.exp y - 8 - 8 * y
  have := Real.add_one_le_exp y
  linarith

/-- An actual uniform bound, stronger than the manuscript's requested bound. -/
theorem W_le_eight (y : ℝ) : W y ≤ 8 := by
  by_cases hy : y = 0
  · simp [hy]
  · simp only [W, hy, ↓reduceIte]
    rcases lt_or_gt_of_ne hy with hneg | hpos
    · have hd : Real.exp y - 1 < 0 := sub_neg.mpr (Real.exp_lt_one_iff.mpr hneg)
      apply (div_le_iff_of_neg hd).2
      have hf : F8 y ≤ 0 := by simpa using F8_monotone hneg.le
      unfold F8 at hf
      nlinarith
    · have hd : 0 < Real.exp y - 1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr hpos)
      apply (div_le_iff₀ hd).2
      have hf : 0 ≤ F8 y := by simpa using F8_monotone hpos.le
      unfold F8 at hf
      nlinarith

/-- The bound is attained by the actual function at its removable value. -/
theorem W_range_isGreatest : IsGreatest (range W) (8 : ℝ) := by
  constructor
  · exact ⟨0, W_zero⟩
  · rintro z ⟨y, rfl⟩
    exact W_le_eight y

/-- Exact global supremum; nonemptiness and boundedness are supplied explicitly. -/
theorem W_sup_eq_eight : sSup (range W) = (8 : ℝ) := by
  have hb : BddAbove (range W) := ⟨8, W_range_isGreatest.2⟩
  apply le_antisymm
  · exact csSup_le (range_nonempty W) W_range_isGreatest.2
  · exact le_csSup hb W_range_isGreatest.1

/-- The manuscript's strict uniform bound, rather than merely pointwise strictness. -/
theorem W_sup_lt_nine : sSup (range W) < (9 : ℝ) := by
  rw [W_sup_eq_eight]
  norm_num

/-- The log-radius potential in the manuscript's scalar normalization. -/
def Wlog (t : ℝ) : ℝ := W (Real.exp (2 * t) / 4 - 2)

theorem Wlog_le_eight (t : ℝ) : Wlog t ≤ 8 := W_le_eight _

/-- The log-radius parametrization contains the actual maximizer. -/
theorem Wlog_at_maximizer : Wlog (Real.log 8 / 2) = 8 := by
  have he : Real.exp (2 * (Real.log 8 / 2)) = (8 : ℝ) := by
    rw [show 2 * (Real.log 8 / 2) = Real.log 8 by ring]
    exact Real.exp_log (by norm_num)
  norm_num [Wlog, he]

theorem Wlog_sup_eq_eight : sSup (range Wlog) = (8 : ℝ) := by
  have hg : IsGreatest (range Wlog) (8 : ℝ) := by
    constructor
    · exact ⟨Real.log 8 / 2, Wlog_at_maximizer⟩
    · rintro z ⟨t, rfl⟩
      exact Wlog_le_eight t
  apply le_antisymm
  · exact csSup_le (range_nonempty Wlog) hg.2
  · exact le_csSup ⟨8, hg.2⟩ hg.1

theorem Wlog_sup_lt_nine : sSup (range Wlog) < (9 : ℝ) := by
  rw [Wlog_sup_eq_eight]
  norm_num

end UnforcedLeray.GaussianPotential
