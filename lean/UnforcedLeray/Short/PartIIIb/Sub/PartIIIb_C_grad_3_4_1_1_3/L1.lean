import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_1.Decomp
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4.L2
import UnforcedLeray.Units.B0146.LatticeSums

/-!
# `PartIII-b:C/grad/3/4/1/1/3/1`: local Gaussian majorant of the lattice weight

Source `the November 2 reference manuscript`
4963-4980, 5036-5039, 5063-5079.

For `|d|, |e| ≤ 1`, shifting the point by `(d, e)` costs at most a factor `3^12 e^{2/9}` in the
weight and halves the Gaussian rate: `(u+d)² ≥ u²/2 - d²`.  Hence on the sup-ball of radius `1`
around `x0` the `j`-th weight is dominated by `M · g j` with
`g j = latticeW (gradAlpha/2) gradK (x0.1 - j c) x0.2`, which is summable.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `u²/2 - d² ≤ (u+d)²` (from `(u+2d)² ≥ 0`). -/
lemma gradW_sq_shift_ge (u d : ℝ) : u ^ 2 / 2 - d ^ 2 ≤ (u + d) ^ 2 := by
  nlinarith [sq_nonneg (u + 2 * d)]

/-- Gaussian shift: the rate halves at a cost `e^{2/9}` for `|d|, |e| ≤ 1`. -/
lemma gradW_exp_shift (u0 η0 d e : ℝ) (hd : |d| ≤ 1) (he : |e| ≤ 1) :
    Real.exp (-(1 / 9) * ((u0 + d) ^ 2 + (η0 + e) ^ 2)) ≤
      Real.exp (2 / 9) * Real.exp (-(1 / 9 / 2) * (u0 ^ 2 + η0 ^ 2)) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hd2 : d ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one d).mpr hd
  have he2 : e ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one e).mpr he
  have key1 := gradW_sq_shift_ge u0 d
  have key2 := gradW_sq_shift_ge η0 e
  linarith

/-- Pointwise shift bound for the lattice weight (real variables). -/
lemma gradW_shift_le (u0 η0 d e : ℝ) (hd : |d| ≤ 1) (he : |e| ≤ 1) :
    latticeW gradAlpha gradK (u0 + d) (η0 + e) ≤
      (3 : ℝ) ^ 12 * Real.exp (2 / 9) * latticeW (gradAlpha / 2) gradK u0 η0 := by
  unfold latticeW gradAlpha gradK
  have hP1 : 1 + |u0 + d| + |η0 + e| ≤ 3 * (1 + |u0| + |η0|) := by
    have h1 := abs_add_le u0 d
    have h2 := abs_add_le η0 e
    linarith [abs_nonneg u0, abs_nonneg η0]
  have hPow : (1 + |u0 + d| + |η0 + e|) ^ 12 ≤ (3 * (1 + |u0| + |η0|)) ^ 12 :=
    pow_le_pow_left₀ (by positivity) hP1 12
  have hPow' : (3 * (1 + |u0| + |η0|)) ^ 12 = (3 : ℝ) ^ 12 * (1 + |u0| + |η0|) ^ 12 := by
    rw [mul_pow]
  have hE := gradW_exp_shift u0 η0 d e hd he
  have hEnn : 0 ≤ Real.exp (-(1 / 9) * ((u0 + d) ^ 2 + (η0 + e) ^ 2)) := (Real.exp_pos _).le
  calc (1 + |u0 + d| + |η0 + e|) ^ 12 * Real.exp (-(1 / 9) * ((u0 + d) ^ 2 + (η0 + e) ^ 2))
      ≤ ((3 : ℝ) ^ 12 * (1 + |u0| + |η0|) ^ 12) *
          (Real.exp (2 / 9) * Real.exp (-(1 / 9 / 2) * (u0 ^ 2 + η0 ^ 2))) :=
        mul_le_mul (hPow.trans hPow'.le) hE hEnn (by positivity)
    _ = (3 : ℝ) ^ 12 * Real.exp (2 / 9) *
          ((1 + |u0| + |η0|) ^ 12 * Real.exp (-(1 / 9 / 2) * (u0 ^ 2 + η0 ^ 2))) := by ring

/-- Local Gaussian majorant of the lattice weight on the sup-ball of radius `1` around `x0`
(source 5063-5079). -/
theorem gradW_ball_majorant (ν : ℝ) (hν : 0 < ν) (x0 : ℝ × ℝ) :
    ∃ (M : ℝ) (g : ℤ → ℝ), 0 ≤ M ∧ Summable g ∧
      ∀ (y : ℝ × ℝ), dist y x0 ≤ 1 → ∀ j : ℤ, gradW ν y j ≤ M * g j := by
  refine ⟨(3 : ℝ) ^ 12 * Real.exp (2 / 9),
    fun j => latticeW (gradAlpha / 2) gradK (x0.1 - (j : ℝ) * cOf ν) x0.2, by positivity, ?_, ?_⟩
  · have hc : 0 < cOf ν := by unfold cOf; positivity
    have hβ : (0 : ℝ) < gradAlpha / 2 / 2 := by unfold gradAlpha; norm_num
    have hsum : Summable (fun j : ℤ => Real.exp (-((gradAlpha / 2 / 2) * (x0.1 - (j : ℝ) * cOf ν) ^ 2))) :=
      UnforcedLeray.B0146.summable_exp_shift hβ hc.ne' x0.1
    have hα : (0 : ℝ) < gradAlpha / 2 := by unfold gradAlpha; norm_num
    have hsum' := hsum.mul_left (Real.exp ((gradK : ℝ) ^ 2 / (2 * (gradAlpha / 2))) ^ 2 *
      Real.exp (-((gradAlpha / 2) / 2) * x0.2 ^ 2))
    refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_) hsum'
    · unfold latticeW
      positivity
    · have h := gl2_W_le (gradAlpha / 2) hα gradK (x0.1 - (j : ℝ) * cOf ν) x0.2
      refine h.trans (le_of_eq ?_)
      simp only [neg_mul]
  · intro y hy j
    have hp := hy
    rw [Prod.dist_eq, max_le_iff, Real.dist_eq, Real.dist_eq] at hp
    obtain ⟨h1, h2⟩ := hp
    have key := gradW_shift_le (x0.1 - (j : ℝ) * cOf ν) x0.2 (y.1 - x0.1) (y.2 - x0.2) h1 h2
    have e1 : x0.1 - (j : ℝ) * cOf ν + (y.1 - x0.1) = y.1 - (j : ℝ) * cOf ν := by ring
    have e2 : x0.2 + (y.2 - x0.2) = y.2 := by ring
    rw [e1, e2] at key
    show gradW ν y j ≤ (3 : ℝ) ^ 12 * Real.exp (2 / 9) *
      latticeW (gradAlpha / 2) gradK (x0.1 - (j : ℝ) * cOf ν) x0.2
    unfold gradW
    exact key

end UnforcedLeray.Short.PartIIIb.Concrete
