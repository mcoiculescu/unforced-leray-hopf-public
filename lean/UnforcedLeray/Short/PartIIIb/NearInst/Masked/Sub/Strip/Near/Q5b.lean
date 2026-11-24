import UnforcedLeray.Short.PartIIIa.SeparatedKernels
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_masked_22_2

/-!
# `PartIII-b:C/near/masked/22/2/5b`: the `L²_τ L²_y` identity for `ltauLq` (source 4000-4003)

`ltauLq P 2 f = ((1/P) ∫_{(0,P]} (∫ f² dy) dτ)^{1/2}`, so squaring and multiplying by `P`
gives the integral over `(0,P]`, which equals the integral over `[0,P)` (null set `{0, P}`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

theorem ltauLq_two_eq (P : ℝ) (hP : 0 < P) (f : ℝ → UnforcedLeray.Space → ENNReal) :
    ENNReal.ofReal P * UnforcedLeray.Short.IIIa.ltauLq P 2 f ^ (2 : ℝ) =
      ∫⁻ τ in Set.Ico (0 : ℝ) P, ∫⁻ y : UnforcedLeray.Space, f τ y ^ (2 : ℝ) := by
  unfold UnforcedLeray.Short.IIIa.ltauLq
  have h22 : ∀ a : ENNReal, a ^ ((2 : ℝ) / 2) = a := by
    intro a
    norm_num
  have hPpos : ENNReal.ofReal P ≠ 0 := (ENNReal.ofReal_pos.2 hP).ne'
  have hPtop : ENNReal.ofReal P ≠ ∞ := ENNReal.ofReal_ne_top
  rw [← ENNReal.rpow_mul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one]
  rw [← mul_assoc, ENNReal.mul_inv_cancel hPpos hPtop, one_mul]
  simp only [h22]
  rw [setLIntegral_congr (Ico_ae_eq_Ioc (μ := volume))]

end UnforcedLeray.Short.PartIIIb.NearInst.Masked
