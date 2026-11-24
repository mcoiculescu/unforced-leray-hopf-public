import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_10_1.H3

/-!
# Helpers for `wardX0YoungL2_proved` (4): the `Y₂` moment of the cut old source

Source of record: `the November 2 reference manuscript` (73 pages),
4155-4156, 2684-2687 (lift identity), 2666-2679 (age weights).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- The squared `L²_τL²` norm of the cut old source is `πR²‖g‖²_{L²(s^{-1/2}dς)}` at most. -/
theorem w10_src_sq (R c r : ℝ) (g : Chart → Ten3) (hR : 0 < R) (hc : 0 < c) (hg : Measurable g) :
    IIIa.ltauLq (2 * c / R) 2 (IIIa.srcNorm (oldCutSrc R c r g)) ^ (2 : ℝ) ≤
      ENNReal.ofReal (Real.pi * R ^ 2) * ∫⁻ p, ‖g p‖ₑ ^ 2 ∂(ageμ c (-1 / 2)) := by
  have hP0 : 0 < 2 * c / R := div_pos (mul_pos two_pos hc) hR
  have hG2 : Measurable fun p : Chart => ‖g p‖ₑ ^ 2 := hg.enorm.pow_const 2
  have hFm : Measurable fun p : Chart => ENNReal.ofReal (p.1 ^ 2) * ‖g p‖ₑ ^ 2 :=
    ((measurable_fst.pow_const 2).ennreal_ofReal).mul hG2
  have hAW : ∫⁻ p, ENNReal.ofReal (p.1 ^ 2) * ‖g p‖ₑ ^ 2 ∂(ageμ c (-5 / 2))
      = ∫⁻ p, ‖g p‖ₑ ^ 2 ∂(ageμ c (-1 / 2)) :=
    ageWeightShift c hc _ hG2
  have hMain : ∫⁻ τ in Ioc 0 (2 * c / R), ∫⁻ z,
      ENNReal.ofReal ((NearInst.chartOf R c z τ).1 ^ 2) *
        ‖g (NearInst.chartOf R c z τ)‖ₑ ^ 2
      = ENNReal.ofReal (2 * c / R) * ENNReal.ofReal (Real.pi * R ^ 2) *
        ∫⁻ p, ENNReal.ofReal (p.1 ^ 2) * ‖g p‖ₑ ^ 2 ∂(ageμ c (-5 / 2)) :=
    chartPhaseLIntegral R c hR hc _ hFm
  rw [hAW] at hMain
  have hB : ∫⁻ τ in Ioc 0 (2 * c / R), (∫⁻ y, IIIa.srcNorm (oldCutSrc R c r g) τ y ^ (2 : ℝ)) ^
      ((2 : ℝ) / 2) ≤ ∫⁻ τ in Ioc 0 (2 * c / R), ∫⁻ z,
        ENNReal.ofReal ((NearInst.chartOf R c z τ).1 ^ 2) *
          ‖g (NearInst.chartOf R c z τ)‖ₑ ^ 2 := by
    refine lintegral_mono fun τ => ?_
    rw [show (2 : ℝ) / 2 = 1 by norm_num, ENNReal.rpow_one]
    exact lintegral_mono fun z => oldCut_sq_le R c r g τ z
  rw [hMain] at hB
  unfold IIIa.ltauLq
  rw [← ENNReal.rpow_mul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one]
  have hPpos : ENNReal.ofReal (2 * c / R) ≠ 0 := (ENNReal.ofReal_pos.2 hP0).ne'
  calc (ENNReal.ofReal (2 * c / R))⁻¹ * ∫⁻ τ in Ioc 0 (2 * c / R),
        (∫⁻ y, IIIa.srcNorm (oldCutSrc R c r g) τ y ^ (2 : ℝ)) ^ ((2 : ℝ) / 2)
      ≤ (ENNReal.ofReal (2 * c / R))⁻¹ * (ENNReal.ofReal (2 * c / R) *
          ENNReal.ofReal (Real.pi * R ^ 2) * ∫⁻ p, ‖g p‖ₑ ^ 2 ∂(ageμ c (-1 / 2))) := by
        exact mul_le_mul_of_nonneg_left hB zero_le
    _ = ENNReal.ofReal (Real.pi * R ^ 2) * ∫⁻ p, ‖g p‖ₑ ^ 2 ∂(ageμ c (-1 / 2)) := by
        rw [← mul_assoc, ← mul_assoc, ENNReal.inv_mul_cancel hPpos ENNReal.ofReal_ne_top, one_mul]

end UnforcedLeray.Short.PartIIIb.Concrete
end
