import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_2_5

/-!
# Change of variables `l = e^s` (`PartIII-b:IIIb-D2/3/1/1/2/5/5`)

On `(0,1)` the map `s ↦ e^s` is a diffeomorphism from `(-∞,0)` with derivative `e^s`, and
`l^a = e^{a s}`, so `l^a dl = e^{(a+1)s} ds` (3631-3646).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem l5ChangeVar : L5ChangeVar := by
  intro g hg a τ
  have himg : Real.exp '' Iio (0 : ℝ) = Ioo 0 1 := by
    rw [Real.image_exp_Iio, Real.exp_zero]
  calc ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal (l ^ a) * g (τ + 2 * Real.log l)
      = ∫⁻ l in Real.exp '' Iio (0 : ℝ), ENNReal.ofReal (l ^ a) * g (τ + 2 * Real.log l) := by
        rw [himg]
    _ = ∫⁻ x in Iio (0 : ℝ), ENNReal.ofReal |Real.exp x| *
          (ENNReal.ofReal (Real.exp x ^ a) * g (τ + 2 * Real.log (Real.exp x))) :=
        lintegral_image_eq_lintegral_abs_deriv_mul (f := Real.exp) (f' := Real.exp)
          measurableSet_Iio (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
          Real.exp_injective.injOn _
    _ = ∫⁻ s in Iio (0 : ℝ), ENNReal.ofReal (Real.exp ((a + 1) * s)) * g (τ + 2 * s) := by
        refine lintegral_congr fun x => ?_
        have h1 : ENNReal.ofReal (Real.exp x) * ENNReal.ofReal (Real.exp (x * a)) =
            ENNReal.ofReal (Real.exp ((a + 1) * x)) := by
          rw [← ENNReal.ofReal_mul (Real.exp_pos x).le, ← Real.exp_add]
          congr 2
          ring
        rw [abs_of_pos (Real.exp_pos x), Real.rpow_def_of_pos (Real.exp_pos x), Real.log_exp,
          ← mul_assoc, h1]

end UnforcedLeray.Short.PartIIIb.Concrete
