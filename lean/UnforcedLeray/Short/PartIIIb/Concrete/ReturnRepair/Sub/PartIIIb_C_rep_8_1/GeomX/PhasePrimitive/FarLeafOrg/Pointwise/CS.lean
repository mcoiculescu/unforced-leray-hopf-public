import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Cauchy-Schwarz over one phase period (helper for `OscFarPt`)
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete.FarLeafOrg

theorem cs_phase (c : ℝ) (hc : 0 < c) (t : ℝ → ℝ) (ht : Measurable t) (ht0 : ∀ q, 0 ≤ t q) :
    ∫⁻ q in Ioc 0 c, ENNReal.ofReal (t q) ≤
      ENNReal.ofReal c * (∫⁻ q in Ioc 0 c, ENNReal.ofReal c⁻¹ * ENNReal.ofReal (t q ^ 2)) ^
        (1 / 2 : ℝ) := by
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict (Ioc (0 : ℝ) c))
    (Real.HolderConjugate.two_two) (f := fun _ => (1 : ℝ≥0∞)) (g := fun q => ENNReal.ofReal (t q))
    aemeasurable_const (ENNReal.measurable_ofReal.comp ht).aemeasurable
  simp only [Pi.mul_apply, one_mul, ENNReal.one_rpow, lintegral_const, Measure.restrict_apply_univ,
    Real.volume_Ioc, sub_zero, one_mul] at hH
  have hsq : ∫⁻ q in Ioc 0 c, ENNReal.ofReal (t q) ^ (2 : ℝ) =
      ∫⁻ q in Ioc 0 c, ENNReal.ofReal (t q ^ 2) := by
    refine lintegral_congr (fun q => ?_)
    rw [ENNReal.ofReal_pow (ht0 q)]
    norm_cast
  rw [hsq] at hH
  refine hH.trans ?_
  have hX : ∫⁻ q in Ioc 0 c, ENNReal.ofReal c⁻¹ * ENNReal.ofReal (t q ^ 2) =
      ENNReal.ofReal c⁻¹ * ∫⁻ q in Ioc 0 c, ENNReal.ofReal (t q ^ 2) :=
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  rw [hX, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  have hc2 : ENNReal.ofReal c = ENNReal.ofReal c ^ (1 / 2 : ℝ) * ENNReal.ofReal c ^ (1 / 2 : ℝ) := by
    rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
    norm_num
  have hone : ENNReal.ofReal c ^ (1 / 2 : ℝ) * ENNReal.ofReal c⁻¹ ^ (1 / 2 : ℝ) = 1 := by
    rw [← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.ofReal_mul hc.le,
      mul_inv_cancel₀ hc.ne']
    simp
  generalize ENNReal.ofReal c ^ (1 / 2 : ℝ) = A at hc2 hone ⊢
  generalize ENNReal.ofReal c⁻¹ ^ (1 / 2 : ℝ) = B at hone ⊢
  generalize (∫⁻ q in Ioc 0 c, ENNReal.ofReal (t q ^ 2)) ^ (1 / 2 : ℝ) = X
  rw [hc2]
  exact le_of_eq (by rw [← mul_assoc, mul_assoc A A B, hone, mul_one])

end UnforcedLeray.Short.PartIIIb.Concrete.FarLeafOrg
