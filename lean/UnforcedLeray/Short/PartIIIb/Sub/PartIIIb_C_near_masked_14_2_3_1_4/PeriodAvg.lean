import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_14_2_3_1_4.Assembly
import UnforcedLeray.Lib.BochnerTime.Periodic
import UnforcedLeray.Lib.Axisymmetric.RingMeasure

/-!
# `PeriodAvg` (`PartIII-b:C/near/masked/14/2/3/1/4`; source 3604-3610)

Source: `the November 2 reference manuscript`.
Substitution `τ = 2q/R + a` over the cell `[-c/2, c/2)` and translation invariance over one period.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

theorem periodAvg : PeriodAvg := by
  intro R c hR hc G hG hper a
  -- `H q = G (2 q / R + a)` is `c`-periodic
  set H : ℝ → ℝ≥0∞ := fun q => G (2 * q / R + a) with hH
  have hHper : Function.Periodic H c := by
    intro q
    simp only [hH]
    have : 2 * (q + c) / R + a = (2 * q / R + a) + 2 * c / R := by field_simp; ring
    rw [this]; exact hper _
  have hk : 0 < R / 2 := by positivity
  have hmain := lintegral_periodic_affine (c := c) (k := R / 2) hc hk H hHper 0
  have hc' : c / (R / 2) = 2 * c / R := by field_simp
  have hG' : ∀ τ, H (R / 2 * τ + 0) = G (τ + a) := by
    intro τ; simp only [hH]; congr 1; field_simp; ring
  simp_rw [hG', hc'] at hmain
  have hper' : Function.Periodic G (2 * c / R) := fun τ => hper τ
  rw [UnforcedLeray.BochnerTime.lintegral_Ioc_comp_add_right (by positivity) hper' a] at hmain
  -- hmain : ∫ G = ofReal (R/2)⁻¹ * ∫_{Ico} H
  have hinv : ENNReal.ofReal (R / 2) * ENNReal.ofReal ((R / 2)⁻¹) = 1 := by
    rw [← ENNReal.ofReal_mul hk.le, mul_inv_cancel₀ hk.ne']; simp
  show ∫⁻ q in Ico (-c / 2) (c / 2), H q = _
  rw [hmain, ← mul_assoc, hinv, one_mul]

end UnforcedLeray.Short.PartIIIb.NearInst.Masked
