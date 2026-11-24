import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_2_2

/-!
# Part II-b, task `PartII-b:T22/2/2/8`: the fundamental theorem with a bounded derivative (`rtdFTC`)

Source of record: `the November 2 reference manuscript`, lines 2074-2105 (pure
real analysis). The derivative `f'` agrees with the measurable function `deriv f` on `(a, b)`, is
bounded there, hence integrable on `(a, b)`; the Mathlib fundamental theorem for interval
integrals then gives `∫_a^b f' = f b - f a`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.IIb

theorem rtdFTC : UnforcedLeray.Short.IIb.RtdFTC := by
  intro f f' a b hab hf hd hbd
  obtain ⟨C, hC⟩ := hbd
  have hmeas : AEStronglyMeasurable f' (volume.restrict (Ioo a b)) := by
    refine (measurable_deriv f).aestronglyMeasurable.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact (hd x hx).deriv
  have hc : IntegrableOn (fun _ : ℝ => C) (Ioo a b) :=
    integrableOn_const measure_Ioo_lt_top.ne
  have hint : IntegrableOn f' (Ioo a b) := by
    refine Integrable.mono' hc hmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    rw [Real.norm_eq_abs]
    exact hC x hx
  have hI : IntervalIntegrable f' volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
    first
      | exact hint.congr_set_ae Ioo_ae_eq_Ioc.symm
      | exact hint.congr_set_ae Ioo_ae_eq_Ioc
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hf (fun x hx => hd x hx) hI

end UnforcedLeray.Short.IIb
