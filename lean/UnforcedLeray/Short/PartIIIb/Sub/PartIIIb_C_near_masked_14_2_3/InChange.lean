import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_14_2_3
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_1.L1
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_1.L4
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_1.L5
import UnforcedLeray.Short.PartIIIa.Compose
import UnforcedLeray.Lib.BochnerTime.Periodic

/-!
# `CartInput` (`PartIII-b:C/near/masked/14/2/3/3`; source 3604-3610, 2666-2683)

Pointwise `|cartLift f (τ+a) z| ≤ s |f(chartOf z (τ+a))|` (`cartLiftFrobBound`); the `z`-integral of
a function of the chart point is `2c/R`-periodic in `τ` (`chartOf_add_int_period`), so the shift is
absorbed over one period (`BochnerTime.lintegral_Ioc_comp_add_right`); then `chartPhaseLIntegral`
and two applications of `lintegral_ageμ_succ` turn `s² ‖f‖²` on `ageμ c (-5/2)` into `‖f‖²` on
`ageμ c (-1/2)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst

theorem cartInput : UnforcedLeray.Short.PartIIIb.NearInst.Masked.CartInput := by
  intro R c hR hc
  refine ⟨ENNReal.ofReal (2 * c / R) * ENNReal.ofReal (Real.pi * R ^ 2),
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top, ?_⟩
  intro f hf a
  have hP0 : 0 < 2 * c / R := div_pos (mul_pos two_pos hc) hR
  set P := 2 * c / R with hPdef
  set H : Chart → ℝ≥0∞ := fun p => ENNReal.ofReal p.1 * (ENNReal.ofReal p.1 * ‖f p‖ₑ ^ (2 : ℝ))
    with hH
  have hHm : Measurable H :=
    (ENNReal.measurable_ofReal.comp measurable_fst).mul
      ((ENNReal.measurable_ofReal.comp measurable_fst).mul (hf.measurable.enorm.pow_const _))
  have hpt : ∀ τ z, ENNReal.ofReal (liftNorm R c f τ z) ^ (2 : ℝ) ≤ H (chartOf R c z τ) := by
    intro τ z
    have hb : liftNorm R c f τ z ≤ (chartOf R c z τ).1 * ‖f (chartOf R c z τ)‖ :=
      cartLiftFrobBound R c f τ z
    have hs0 : 0 ≤ (chartOf R c z τ).1 := by
      show 0 ≤ R ^ 2 / hRad z ^ 2
      positivity
    calc ENNReal.ofReal (liftNorm R c f τ z) ^ (2 : ℝ)
        ≤ ENNReal.ofReal ((chartOf R c z τ).1 * ‖f (chartOf R c z τ)‖) ^ (2 : ℝ) := by
          gcongr
      _ = H (chartOf R c z τ) := by
          rw [ENNReal.ofReal_mul hs0, ofReal_norm,
            ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2), hH]
          simp only
          rw [ENNReal.rpow_two, pow_two]
          ring
  set Φ : ℝ → ℝ≥0∞ := fun τ => ∫⁻ z, H (chartOf R c z τ) with hΦ
  have hper : Function.Periodic Φ P := by
    intro τ
    simp only [hΦ]
    refine lintegral_congr fun z => ?_
    have := chartOf_add_int_period R c hR hc z τ 1
    simp only [Int.cast_one, one_mul] at this
    rw [this]
  calc ∫⁻ τ in Ioc (0 : ℝ) P, ∫⁻ z : Space,
        ENNReal.ofReal (liftNorm R c f (τ + a) z) ^ (2 : ℝ)
      ≤ ∫⁻ τ in Ioc (0 : ℝ) P, Φ (τ + a) := by
        refine lintegral_mono fun τ => ?_
        exact lintegral_mono fun z => hpt _ _
    _ = ∫⁻ τ in Ioc (0 : ℝ) P, Φ τ :=
        UnforcedLeray.BochnerTime.lintegral_Ioc_comp_add_right hP0 hper a
    _ = ENNReal.ofReal P * ENNReal.ofReal (Real.pi * R ^ 2) * ∫⁻ p, H p ∂(ageμ c (-5 / 2)) :=
        chartPhaseLIntegral R c hR hc H hHm
    _ = ENNReal.ofReal P * ENNReal.ofReal (Real.pi * R ^ 2) *
          ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂(ageμ c (-1 / 2)) := by
        congr 1
        have hm1 : Measurable fun p : Chart => ENNReal.ofReal p.1 * ‖f p‖ₑ ^ (2 : ℝ) :=
          (ENNReal.measurable_ofReal.comp measurable_fst).mul
            (hf.measurable.enorm.pow_const _)
        have hm0 : Measurable fun p : Chart => ‖f p‖ₑ ^ (2 : ℝ) :=
          hf.measurable.enorm.pow_const _
        have e1 := UnforcedLeray.Short.IIIa.lintegral_ageμ_succ hc (-5 / 2) hm1
        have e0 := UnforcedLeray.Short.IIIa.lintegral_ageμ_succ hc (-3 / 2) hm0
        rw [show (-5 / 2 : ℝ) + 1 = -3 / 2 by norm_num] at e1
        rw [show (-3 / 2 : ℝ) + 1 = -1 / 2 by norm_num] at e0
        rw [e0]
        exact e1.symm

end UnforcedLeray.Short.PartIIIb.NearInst.Masked
