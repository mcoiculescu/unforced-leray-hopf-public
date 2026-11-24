import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4_1_1.Decomp
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_grad_3_4.L2
import UnforcedLeray.Units.B0146.LatticeSums

/-!
# `PartIII-b:C/grad/3/4/1/1/1`: summability of the Gaussian lattice sum (leaf C)

Source `the November 2 reference manuscript`
5063-5079.  Proved: `gradLatticeSummable`.

Route: the weight `latticeW gradAlpha gradK` is dominated by a constant times the `u`-Gaussian
`exp(-(α/2) u²)` (`gl2_W_le`), and a Gaussian lattice translate with spacing `c ≠ 0` is summable
(`UnforcedLeray.B0146.summable_exp_shift`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem gradLatticeSummable : GradLatticeSummable := by
  intro c hc x
  have hα : (0 : ℝ) < gradAlpha := by norm_num [gradAlpha]
  have hβ : (0 : ℝ) < gradAlpha / 2 := by linarith
  have hsum : Summable (fun j : ℤ => Real.exp (-((gradAlpha / 2) * (x.1 - (j : ℝ) * c) ^ 2))) :=
    UnforcedLeray.B0146.summable_exp_shift hβ hc.ne' x.1
  have hsum' := hsum.mul_left (Real.exp ((gradK : ℝ) ^ 2 / (2 * gradAlpha)) ^ 2 *
    Real.exp (-(gradAlpha / 2) * x.2 ^ 2))
  refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_) hsum'
  · unfold latticeW
    positivity
  · have h := gl2_W_le gradAlpha hα gradK (x.1 - (j : ℝ) * c) x.2
    refine h.trans (le_of_eq ?_)
    simp only [neg_mul]

end UnforcedLeray.Short.PartIIIb.Concrete
