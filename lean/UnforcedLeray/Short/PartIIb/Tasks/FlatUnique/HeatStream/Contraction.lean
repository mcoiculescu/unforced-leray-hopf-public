import UnforcedLeray.Short.PartIIb.Sub.T11_3
import UnforcedLeray.Lib.CylinderB.Periodize

/-!
# Part II-b, leaf `PartII-b:T11/3/5` (`HeatConvContraction`): heat contraction on the cylinder

Source of record: `the November 2 reference manuscript`, SP 1923-1927 (the heat
semigroup is an `L^p` contraction on the cylinder). The statement is `HeatConvContraction` of
`Sub/T11_3.lean`.

Proof. `Cyl.eLpNorm_planarConv_periodic_le` with the planar heat kernel `k = heatKernel2 θ`,
which has unit mass (`integral_heatKernel2`, `heatKernel2_nonneg`), gives
`‖G_θ * f‖_{L^p(cell)} ≤ ‖f‖_{L^p(cell)}`. The `L^p` norms are converted to lower integrals of
`‖·‖ₑ ^ p` and the power `1/p` is removed. The normalized measure `Cyl.avgμ c` is
`ofReal c⁻¹ • Cyl.cellμ c`, so the common factor `ofReal c⁻¹` is pulled out of both sides.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb

/-- The planar heat kernel is measurable. -/
theorem heatConv_measurable_heatKernel2 (θ : ℝ) :
    Measurable (UnforcedLeray.B0284.heatKernel2 θ) := by
  unfold UnforcedLeray.B0284.heatKernel2 UnforcedLeray.B0191.heatKernel
  fun_prop

/-- The planar heat kernel is integrable (`θ > 0`): its integral is `1 ≠ 0`. -/
theorem heatConv_integrable_heatKernel2 {θ : ℝ} (hθ : 0 < θ) :
    Integrable (UnforcedLeray.B0284.heatKernel2 θ) := by
  refine Integrable.of_integral_ne_zero ?_
  rw [UnforcedLeray.B0284.integral_heatKernel2 hθ]
  exact one_ne_zero

/-- The planar heat kernel has unit `L¹` norm (`θ > 0`). -/
theorem heatConv_eLpNorm_heatKernel2_one {θ : ℝ} (hθ : 0 < θ) :
    eLpNorm (UnforcedLeray.B0284.heatKernel2 θ) 1 volume = 1 := by
  rw [eLpNorm_one_eq_lintegral_enorm]
  have hnn : ∀ w : ℝ × ℝ, 0 ≤ UnforcedLeray.B0284.heatKernel2 θ w :=
    fun w => UnforcedLeray.B0284.heatKernel2_nonneg hθ w
  have h := ofReal_integral_eq_lintegral_ofReal (heatConv_integrable_heatKernel2 hθ)
    (Filter.Eventually.of_forall hnn)
  rw [UnforcedLeray.B0284.integral_heatKernel2 hθ, ENNReal.ofReal_one] at h
  have hcongr : ∫⁻ w, ‖UnforcedLeray.B0284.heatKernel2 θ w‖ₑ ∂volume =
      ∫⁻ w, ENNReal.ofReal (UnforcedLeray.B0284.heatKernel2 θ w) ∂volume :=
    lintegral_congr fun w => Real.enorm_of_nonneg (hnn w)
  rw [hcongr, ← h]

/-- **Leaf `PartII-b:T11/3/5`** (`L^p` contraction of Gaussian convolution on the cylinder).
For `c, θ > 0`, `p ≥ 1`, a continuous `c`-periodic `f` vanishing for `|η|` large:
`∫_cell |G_θ * f|^p ≤ ∫_cell |f|^p` with the normalized cell measure `Cyl.avgμ c`. -/
theorem heatConvContraction : UnforcedLeray.Short.IIb.HeatConvContraction := by
  unfold HeatConvContraction
  intro c θ p f hc hθ hp hf hper _hsupp
  have hpos : 0 < p := lt_of_lt_of_le one_pos hp
  have hp0 : (0 : ℝ) ≤ p := hpos.le
  have hq0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.2 hpos).ne'
  have hqtop : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hq1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.2 hp
  have hqtoReal : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp0
  have hkstr : StronglyMeasurable (UnforcedLeray.B0284.heatKernel2 θ) :=
    (heatConv_measurable_heatKernel2 θ).stronglyMeasurable
  have hfstr : StronglyMeasurable f := hf.stronglyMeasurable
  have key := Cyl.eLpNorm_planarConv_periodic_le hc hkstr hfstr hper hq1 hqtop
  rw [heatConv_eLpNorm_heatKernel2_one hθ, one_mul] at key
  simp only [smul_eq_mul] at key
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 hqtop,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 hqtop, hqtoReal] at key
  have hA : (∫⁻ x, ‖∫ y, UnforcedLeray.B0284.heatKernel2 θ y * f (x - y)‖ₑ ^ p ∂Cyl.cellμ c) ≤
      ∫⁻ x, ‖f x‖ₑ ^ p ∂Cyl.cellμ c := by
    have h2 := ENNReal.rpow_le_rpow key hp0
    rwa [← ENNReal.rpow_mul, ← ENNReal.rpow_mul, one_div_mul_cancel hpos.ne', ENNReal.rpow_one,
      ENNReal.rpow_one] at h2
  unfold Cyl.avgμ
  rw [lintegral_smul_measure, lintegral_smul_measure]
  exact mul_le_mul_of_nonneg_left hA zero_le

end UnforcedLeray.Short.IIb
