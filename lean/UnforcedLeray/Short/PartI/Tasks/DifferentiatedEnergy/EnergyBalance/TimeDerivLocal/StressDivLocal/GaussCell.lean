import UnforcedLeray.Lib.Cylinder.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Part I, task `PartI:T08/4/1/1/5/3` (`qcJet_gauss_cell`)

Source: `the November 2 reference manuscript`, lines 326-335 and 2217-2234.

A continuous function on the plane that is bounded by a transverse Gaussian
`A exp(-b z₂²)` is `L²` on the cell and its squared integral is dominated by that of the
Gaussian majorant. The majorant squared is `A² exp(-2b z₂²)`, which is a product of the
constant `1` in `z₁` on the finite interval `Ico (-c/2) (c/2)` and an integrable Gaussian in `z₂`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartI

open MeasureTheory Set

/-- The square of a transverse Gaussian is a Gaussian with doubled rate. -/
lemma gauss_sq_eq_exp (A b y : ℝ) :
    (A * Real.exp (-(b * y ^ 2))) ^ 2 = A ^ 2 * Real.exp (-(2 * b) * y ^ 2) := by
  have h : Real.exp (-(b * y ^ 2)) ^ 2 = Real.exp (-(2 * b) * y ^ 2) := by
    rw [pow_two (Real.exp (-(b * y ^ 2))), ← Real.exp_add]
    congr 1
    ring
  rw [mul_pow, h]

theorem qcJet_gauss_cell {c A b : ℝ} (hb : 0 < b) {F : UnforcedLeray.Cyl.Plane → ℝ} (hF : Continuous F) (h : ∀ z : UnforcedLeray.Cyl.Plane, |F z| ≤ A * Real.exp (-(b * z.2 ^ 2))) : MemLp F 2 (UnforcedLeray.Cyl.cellμ c) ∧ ∫ z in UnforcedLeray.Cyl.cell c, F z ^ 2 ≤ ∫ z in UnforcedLeray.Cyl.cell c, (A * Real.exp (-(b * z.2 ^ 2))) ^ 2 := by
  have hb2 : 0 < 2 * b := by linarith
  have hG_one : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Ico (-c / 2) (c / 2))) :=
    integrableOn_const (by rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top)
  have hG_gauss : Integrable (fun y : ℝ => A ^ 2 * Real.exp (-(2 * b) * y ^ 2)) :=
    (integrable_exp_neg_mul_sq hb2).const_mul (A ^ 2)
  have hmaj : Integrable (fun z : UnforcedLeray.Cyl.Plane => (A * Real.exp (-(b * z.2 ^ 2))) ^ 2)
      (UnforcedLeray.Cyl.cellμ c) := by
    rw [UnforcedLeray.Cyl.cellμ_eq_prod]
    have hp := hG_one.mul_prod hG_gauss
    refine hp.congr (ae_of_all _ fun z => ?_)
    simp only [one_mul]
    exact (gauss_sq_eq_exp A b z.2).symm
  have hsq : ∀ z : UnforcedLeray.Cyl.Plane, F z ^ 2 ≤ (A * Real.exp (-(b * z.2 ^ 2))) ^ 2 := by
    intro z
    calc F z ^ 2 = |F z| ^ 2 := (sq_abs _).symm
      _ ≤ (A * Real.exp (-(b * z.2 ^ 2))) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (h z) 2
  have hF2 : Integrable (fun z : UnforcedLeray.Cyl.Plane => F z ^ 2) (UnforcedLeray.Cyl.cellμ c) := by
    refine hmaj.mono' (hF.pow 2).aestronglyMeasurable (ae_of_all _ fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hsq z
  refine ⟨(memLp_two_iff_integrable_sq hF.aestronglyMeasurable).2 hF2, ?_⟩
  exact integral_mono hF2 hmaj (fun z => hsq z)

end UnforcedLeray.Short.PartI

end
