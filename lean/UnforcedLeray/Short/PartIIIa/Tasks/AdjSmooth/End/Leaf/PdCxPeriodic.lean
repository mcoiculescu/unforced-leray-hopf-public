import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_1_2_1_3_3

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- **Leaf**: the classical derivative of a smooth `c`-periodic function is `c`-periodic
(differentiate `g (· + (c, 0)) = g`). -/
theorem pdCxPeriodic : UnforcedLeray.Short.IIIa.PdCxPeriodic := by
  intro c k g _hg hper x
  have hfun : (fun y : ℝ × ℝ => g (y + ((c, 0) : ℝ × ℝ))) = g := by
    funext y
    have hy : y + ((c, 0) : ℝ × ℝ) = (y.1 + c, y.2) := by ext <;> simp
    rw [hy]
    exact hper y
  have h := fderiv_comp_add_right (𝕜 := ℝ) (f := g) (x := x) ((c, 0) : ℝ × ℝ)
  rw [hfun] at h
  have hx : x + ((c, 0) : ℝ × ℝ) = (x.1 + c, x.2) := by ext <;> simp
  unfold pdCx
  rw [← hx, ← h]

end UnforcedLeray.Short.IIIa
