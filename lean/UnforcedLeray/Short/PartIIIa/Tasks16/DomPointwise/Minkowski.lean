import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T16
import UnforcedLeray.Lib.Kernels.PlanarBS.P.Infra.ConvMinkowski.Minkowski
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Minkowski in the dilation variable for `ltauAt`, and the power integral on `(0,1)`
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

theorem ltauAt_lintegral_le (P : ℝ) (hP : 0 < P) (F : ℝ → ℝ → ℝ≥0∞)
    (hF : Measurable (Function.uncurry F)) :
    ltauAt P (fun τ => ∫⁻ l in Ioo (0 : ℝ) 1, F l τ) ≤
      ∫⁻ l in Ioo (0 : ℝ) 1, ltauAt P (F l) := by
  have hc : ((ENNReal.ofReal P)⁻¹) ^ (1 / 2 : ℝ) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num)
      (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr hP).ne')
  have hF' : AEMeasurable (Function.uncurry fun (τ l : ℝ) => F l τ)
      ((volume.restrict (Ioc 0 P)).prod (volume.restrict (Ioo (0 : ℝ) 1))) := by
    refine Measurable.aemeasurable ?_
    exact hF.comp measurable_swap
  have hM := PlanarBS.Conv.lintegral_lintegral_rpow_le (μ := volume.restrict (Ioc 0 P))
    (ν := volume.restrict (Ioo (0 : ℝ) 1)) hF' (p := 2) (by norm_num)
  unfold ltauAt
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  calc ((ENNReal.ofReal P)⁻¹) ^ (1 / 2 : ℝ) *
        (∫⁻ τ in Ioc 0 P, (∫⁻ l in Ioo (0 : ℝ) 1, F l τ) ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
      ≤ ((ENNReal.ofReal P)⁻¹) ^ (1 / 2 : ℝ) *
        ∫⁻ l in Ioo (0 : ℝ) 1, (∫⁻ τ in Ioc 0 P, F l τ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
        gcongr
    _ = _ := by
        rw [← lintegral_const_mul' _ _ hc]
        refine lintegral_congr fun l => ?_
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]

theorem sepDomPointwise_lintegral_Ioo_rpow (e : ℝ) (he : -1 < e) :
    ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal (l ^ e) = ENNReal.ofReal (1 / (e + 1)) := by
  have hi : IntervalIntegrable (fun x : ℝ => x ^ e) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' he
  have hi2 : IntegrableOn (fun x : ℝ => x ^ e) (Ioo 0 1) volume :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp hi).mono_set Ioo_subset_Ioc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hi2
    (ae_restrict_of_forall_mem measurableSet_Ioo fun x hx => Real.rpow_nonneg hx.1.le _)]
  congr 1
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
    integral_rpow (Or.inl he)]
  rw [Real.zero_rpow (by linarith : e + 1 ≠ 0)]
  simp

end UnforcedLeray.Short.IIIa

end
