import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_1
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_1.L4
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_1.L5
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_1.L6

/-!
# `OldCutMoment` (`PartIII-b:IIIb-D2/3/1/1/1/7`)

Source of record: `the November 2 reference manuscript` 4155-4156 (`T ∈ Y₂`),
2684-2687 (lift identity).  The cut old source `oldCutSrc R c r G` has, for `q = 2`,
`srcNorm(oldCutSrc) τ z ^ 2 ≤ F(chartOf R c z τ)` with `F p = ofReal (p.1 ^ 2) * ‖G p‖ₑ ^ 2`
(`CartLiftFrobBound`; the cut branch vanishes).  Then `ChartPhaseLIntegral` and `AgeWeightShift`
bound the `L²_τL²_z` moment by `ofReal P * ofReal (π R²) * ∫ ‖G‖ₑ² dageμ(-1/2)`, which is finite.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- Scalar step: `ofReal t ^ 2 ≤ ofReal (s ^ 2) * ‖X‖ₑ ^ 2` when `0 ≤ t ≤ s ‖X‖`. -/
theorem oldCut_aux (s : ℝ) (X : Ten3) (t : ℝ) (ht : 0 ≤ t) (h : t ≤ s * ‖X‖) :
    ENNReal.ofReal t ^ 2 ≤ ENNReal.ofReal (s ^ 2) * ‖X‖ₑ ^ 2 := by
  have key : ENNReal.ofReal (s ^ 2) * ‖X‖ₑ ^ 2 = ENNReal.ofReal (s ^ 2 * ‖X‖ ^ 2) := by
    rw [ENNReal.ofReal_mul (sq_nonneg s), ENNReal.ofReal_pow (norm_nonneg X),
      ofReal_norm X]
  rw [key, ← ENNReal.ofReal_pow ht]
  exact ENNReal.ofReal_le_ofReal (by nlinarith [mul_le_mul h h ht (ht.trans h)])

/-- Pointwise squared-source bound: `|oldCutSrc R c r G τ z|² ≤ F(chartOf R c z τ)` for
`F p = ofReal (p.1 ^ 2) * ‖G p‖ₑ ^ 2` (source 2683, the cut branch gives zero). -/
theorem oldCut_sq_le (R c r : ℝ) (G : Chart → Ten3) (τ : ℝ) (z : Space) :
    IIIa.srcNorm (oldCutSrc R c r G) τ z ^ (2 : ℝ) ≤
      ENNReal.ofReal ((NearInst.chartOf R c z τ).1 ^ 2) *
        ‖G (NearInst.chartOf R c z τ)‖ₑ ^ 2 := by
  simp only [IIIa.srcNorm, oldCutSrc]
  rw [ENNReal.rpow_two]
  split_ifs with hz
  · exact oldCut_aux _ _ _ (Real.sqrt_nonneg _) (cartLiftFrobBound R c G τ z)
  · simp [IIIa.tensorNorm]

/-- **`Y₂` moment of the cut old source** (source 4155-4156, lift identity 2684-2687). -/
theorem oldCutMoment : OldCutMoment := by
  intro R c r G hR hc hG hJ
  unfold SepMoment
  unfold IIIa.ltauLq
  have hP0 : 0 < 2 * c / R := div_pos (mul_pos two_pos hc) hR
  have hG2 : Measurable fun p : Chart => ‖G p‖ₑ ^ 2 := hG.enorm.pow_const 2
  have hFm : Measurable fun p : Chart => ENNReal.ofReal (p.1 ^ 2) * ‖G p‖ₑ ^ 2 :=
    ((measurable_fst.pow_const 2).ennreal_ofReal).mul hG2
  have hAW : ∫⁻ p, ENNReal.ofReal (p.1 ^ 2) * ‖G p‖ₑ ^ 2 ∂(ageμ c (-5 / 2))
      = ∫⁻ p, ‖G p‖ₑ ^ 2 ∂(ageμ c (-1 / 2)) :=
    ageWeightShift c hc _ hG2
  have hMain : ∫⁻ τ in Ioc 0 (2 * c / R), ∫⁻ z,
      ENNReal.ofReal ((NearInst.chartOf R c z τ).1 ^ 2) *
        ‖G (NearInst.chartOf R c z τ)‖ₑ ^ 2
      = ENNReal.ofReal (2 * c / R) * ENNReal.ofReal (Real.pi * R ^ 2) *
        ∫⁻ p, ENNReal.ofReal (p.1 ^ 2) * ‖G p‖ₑ ^ 2 ∂(ageμ c (-5 / 2)) :=
    chartPhaseLIntegral R c hR hc _ hFm
  rw [hAW] at hMain
  have hfin : ENNReal.ofReal (2 * c / R) * ENNReal.ofReal (Real.pi * R ^ 2) *
      ∫⁻ p, ‖G p‖ₑ ^ 2 ∂(ageμ c (-1 / 2)) < ⊤ :=
    ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top) hJ
  have hB : ∫⁻ τ in Ioc 0 (2 * c / R), (∫⁻ y, IIIa.srcNorm (oldCutSrc R c r G) τ y ^ (2 : ℝ)) ^
      ((2 : ℝ) / 2) ≤ ∫⁻ τ in Ioc 0 (2 * c / R), ∫⁻ z,
        ENNReal.ofReal ((NearInst.chartOf R c z τ).1 ^ 2) *
          ‖G (NearInst.chartOf R c z τ)‖ₑ ^ 2 := by
    refine lintegral_mono fun τ => ?_
    rw [show (2 : ℝ) / 2 = 1 by norm_num, ENNReal.rpow_one]
    exact lintegral_mono fun z => oldCut_sq_le R c r G τ z
  rw [hMain] at hB
  have hX : (ENNReal.ofReal (2 * c / R))⁻¹ * ∫⁻ τ in Ioc 0 (2 * c / R),
      (∫⁻ y, IIIa.srcNorm (oldCutSrc R c r G) τ y ^ (2 : ℝ)) ^ ((2 : ℝ) / 2) < ⊤ :=
    ENNReal.mul_lt_top (ENNReal.inv_lt_top.2 (ENNReal.ofReal_pos.2 hP0))
      (lt_of_le_of_lt hB hfin)
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hX.ne

end UnforcedLeray.Short.PartIIIb.Concrete
