import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_7
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.Complex.Isometry
import Mathlib.Analysis.Complex.Circle

/-!
# `RotPlMP`: the planar rotation preserves Lebesgue measure (task `PartIII-b:C/srcL/7/1`)

Source of record: `the November 2 reference manuscript`, lines 4776-4782 (the
`x'`-integral over `ℝ²` with Lebesgue measure).

Route: identify `ℝ × ℝ` with `ℂ` by `Complex.measurableEquivRealProd` (measure preserving,
`Complex.volume_preserving_equiv_real_prod`), and recognise `rotPl θ` as the conjugate of Mathlib's
`rotation (Circle.exp θ)` (a linear isometry of `ℂ`, hence measure preserving).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `rotPl θ` is the conjugate of the complex rotation `z ↦ e^{iθ} z` by the identification
`ℂ ≃ ℝ × ℝ`. -/
theorem rotPl_eq_comp (θ : ℝ) :
    rotPl θ = (Complex.measurableEquivRealProd ∘ ⇑(rotation (Circle.exp θ)) ∘
      Complex.measurableEquivRealProd.symm) := by
  funext p
  apply Prod.ext
  · simp [rotPl, Function.comp_apply, rotation_apply, Circle.coe_exp, Complex.mul_re,
      Complex.mul_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      Complex.measurableEquivRealProd_apply, Complex.measurableEquivRealProd_symm_apply]
  · simp [rotPl, Function.comp_apply, rotation_apply, Circle.coe_exp, Complex.mul_re,
      Complex.mul_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      Complex.measurableEquivRealProd_apply, Complex.measurableEquivRealProd_symm_apply]
    ring

theorem rotPlMP : RotPlMP := by
  intro θ
  have he : MeasurePreserving (⇑Complex.measurableEquivRealProd) volume volume :=
    Complex.volume_preserving_equiv_real_prod
  have hR : MeasurePreserving ⇑(rotation (Circle.exp θ)) volume volume :=
    (rotation (Circle.exp θ)).measurePreserving
  have hes : MeasurePreserving ⇑Complex.measurableEquivRealProd.symm volume volume :=
    MeasurePreserving.symm Complex.measurableEquivRealProd he
  rw [rotPl_eq_comp θ]
  exact he.comp (hR.comp hes)

end UnforcedLeray.Short.PartIIIb.Concrete
