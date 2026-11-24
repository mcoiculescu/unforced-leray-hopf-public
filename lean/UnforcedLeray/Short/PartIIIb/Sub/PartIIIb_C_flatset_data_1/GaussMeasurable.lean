import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_data_1
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Real.Sqrt
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- `gaussE a` is continuous (closed form, `a ≠ 0` is not needed for continuity of the expression
since `2 * a` in the denominator is fixed). -/
theorem gm_gaussE_continuous (a : ℝ) : Continuous (gaussE a) := by
  unfold gaussE
  fun_prop

/-- `gaussRdE a` is measurable: `r * deriv (gaussE a) r`, with `deriv` measurable (`measurable_deriv`). -/
theorem gm_gaussRdE_measurable (a : ℝ) : Measurable (gaussRdE a) := by
  unfold gaussRdE
  exact measurable_id.mul (measurable_deriv (gaussE a))

/-- `planeR` is continuous hence measurable. -/
theorem gm_planeR_measurable : Measurable planeR := by
  unfold planeR
  exact (Real.continuous_sqrt.comp (by fun_prop)).measurable

/-- The angular-two function `(x₁ + i x₂)² / |x|²` is measurable (quotient of measurable functions). -/
theorem gm_angTwo_measurable : Measurable IIIa.angTwo := by
  unfold IIIa.angTwo
  exact Measurable.div (by fun_prop) (by fun_prop)

theorem gm_hMode_measurable (a : ℝ) : Measurable (hMode a) := by
  unfold hMode
  exact (Complex.measurable_ofReal.comp ((gm_gaussRdE_measurable a).comp gm_planeR_measurable)).mul
    gm_angTwo_measurable

theorem gm_rMode_measurable (a : ℝ) : Measurable (rMode a) := by
  unfold rMode
  have h1 : Measurable fun x : ℝ × ℝ => gaussRdE a (planeR x) :=
    (gm_gaussRdE_measurable a).comp gm_planeR_measurable
  have h2 : Measurable fun x : ℝ × ℝ => gaussE a (planeR x) :=
    ((gm_gaussE_continuous a).measurable).comp gm_planeR_measurable
  exact Complex.measurable_ofReal.comp (h1.add (measurable_const.mul h2))

/-- **Measurability of the source profiles** (source 4565-4570): `gaussRdE` involves `deriv`, so
`measurable_deriv` is used; `IIIa.angTwo` is a quotient of measurable functions. -/
theorem gaussMeasurable : GaussMeasurable := fun a => ⟨gm_hMode_measurable a, gm_rMode_measurable a⟩

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
