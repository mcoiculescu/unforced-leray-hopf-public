import UnforcedLeray.Lib.HeatCylinder.Gradient

/-!
# Linearity of the actual cylinder heat-divergence kernel

This file proves a.e. additivity for the actual Gaussian convolution on periodic cell `L²` data.
The proof uses the existing Gaussian kernel integrability theory at almost every cell point.
-/

set_option autoImplicit false
set_option maxHeartbeats 500000

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.B0284 (cellMeasure IsQPeriodic)
open UnforcedLeray.GaussianVortex (Plane)

/-- The concrete Gaussian heat-divergence convolution commutes pointwise with translations of its
input and output, for every positive heat age. -/
theorem heatDiv_translate {θ : ℝ} (hθ : 0 < θ) (T : Plane → Plane × Plane)
    (a z : Plane) :
    UnforcedLeray.B0296.heatDiv θ (fun y => T (y + a)) z =
      UnforcedLeray.B0296.heatDiv θ T (z + a) := by
  rw [UnforcedLeray.B0296.heatDiv_apply_of_pos hθ,
    UnforcedLeray.B0296.heatDiv_apply_of_pos hθ]
  apply integral_congr_ae
  filter_upwards [] with w
  have hshift : (z - w) + a = (z + a) - w := by
    ext <;> simp [sub_eq_add_neg] <;> abel
  rw [hshift]

/-- The Gaussian divergence kernel is additive in its tensor argument. -/
theorem divKernel_add (θ : ℝ) (w : Plane) (x y : Plane × Plane) :
    UnforcedLeray.B0296.divKernel θ w (x + y) =
      UnforcedLeray.B0296.divKernel θ w x + UnforcedLeray.B0296.divKernel θ w y := by
  simp [UnforcedLeray.B0296.divKernel]
  ring

/-- The Gaussian divergence kernel is real-linear in its tensor argument. -/
theorem divKernel_smul (θ r : ℝ) (w : Plane) (x : Plane × Plane) :
    UnforcedLeray.B0296.divKernel θ w (r • x) =
      r • UnforcedLeray.B0296.divKernel θ w x := by
  simp [UnforcedLeray.B0296.divKernel, smul_add, smul_smul]
  module

/-- On periodic cell-`L²` data, the actual Gaussian heat-divergence output respects real scalar
multiplication almost everywhere on the cell. -/
theorem heatDiv_smul_ae {c θ r : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    {T : Plane → Plane × Plane} (hper : IsQPeriodic c T)
    (hTm : AEStronglyMeasurable T volume) (hT : MemLp T 2 (cellMeasure c)) :
    UnforcedLeray.B0296.heatDiv θ (fun z => r • T z) =ᵐ[cellMeasure c]
      fun z => r • UnforcedLeray.B0296.heatDiv θ T z := by
  have hperSmul : IsQPeriodic c (fun z => r • T z) := by
    intro z
    simp [hper z]
  have hTmSmul : AEStronglyMeasurable (fun z => r • T z) volume := hTm.const_smul r
  have hTmemSmul : MemLp (fun z => r • T z) 2 (cellMeasure c) := hT.const_smul r
  have hkernelMass : (∫⁻ w : Plane, UnforcedLeray.B0296.gradKernelAbs θ w) ≠ ∞ := by
    rw [UnforcedLeray.B0296.lintegral_gradKernelAbs hθ]
    exact ENNReal.ofReal_ne_top
  have hfinite := UnforcedLeray.B0296.ae_kernelAbs_lt_top'
    hc (UnforcedLeray.B0296.measurable_gradKernelAbs θ)
    (UnforcedLeray.B0296.gradKernelAbs_ne_top θ) hkernelMass hper hTm
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) ENNReal.ofNat_ne_top hT.eLpNorm_ne_top
  filter_upwards [hfinite] with z hz
  have hInt : Integrable
      (fun w : Plane => UnforcedLeray.B0296.divKernel θ w (T (z - w))) :=
    UnforcedLeray.B0296.integrable_kconv_of_lt_top
      (A := UnforcedLeray.B0296.divKernel θ)
      (k := UnforcedLeray.B0296.gradKernelAbs θ)
      (UnforcedLeray.B0296.enorm_divKernel_le θ) z
      (UnforcedLeray.B0296.aestronglyMeasurable_divIntegrand θ hTm z) hz
  rw [UnforcedLeray.B0296.heatDiv_apply_of_pos hθ,
    UnforcedLeray.B0296.heatDiv_apply_of_pos hθ]
  calc
    (∫ w : Plane, UnforcedLeray.B0296.divKernel θ w
        ((fun z => r • T z) (z - w))) =
        ∫ w : Plane, r • UnforcedLeray.B0296.divKernel θ w (T (z - w)) := by
      exact integral_congr_ae (Filter.Eventually.of_forall fun w => by
        change UnforcedLeray.B0296.divKernel θ w (r • T (z - w)) = _
        exact divKernel_smul θ r w _)
    _ = r • ∫ w : Plane, UnforcedLeray.B0296.divKernel θ w (T (z - w)) :=
      Integrable.integral_smul r hInt

/-- On periodic cell-`L²` data, the actual Gaussian heat-divergence output is a.e. additive.
No pointwise convergence is assumed globally: kernel integrability is proved on the a.e. set where
all three convolutions converge. -/
theorem heatDiv_add_ae {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    {T₁ T₂ : Plane → Plane × Plane}
    (hper₁ : IsQPeriodic c T₁) (hper₂ : IsQPeriodic c T₂)
    (hT₁m : AEStronglyMeasurable T₁ volume) (hT₂m : AEStronglyMeasurable T₂ volume)
    (hT₁ : MemLp T₁ 2 (cellMeasure c)) (hT₂ : MemLp T₂ 2 (cellMeasure c)) :
    UnforcedLeray.B0296.heatDiv θ (fun z => T₁ z + T₂ z) =ᵐ[cellMeasure c]
      fun z => UnforcedLeray.B0296.heatDiv θ T₁ z +
        UnforcedLeray.B0296.heatDiv θ T₂ z := by
  have hperSum : IsQPeriodic c (fun z => T₁ z + T₂ z) := by
    intro z
    simp [hper₁ z, hper₂ z]
  have hTsumM : AEStronglyMeasurable (fun z => T₁ z + T₂ z) volume := hT₁m.add hT₂m
  have hTsum : MemLp (fun z => T₁ z + T₂ z) 2 (cellMeasure c) := hT₁.add hT₂
  have hkernelMass : (∫⁻ w : Plane, UnforcedLeray.B0296.gradKernelAbs θ w) ≠ ∞ := by
    rw [UnforcedLeray.B0296.lintegral_gradKernelAbs hθ]
    exact ENNReal.ofReal_ne_top
  have hfinite₁ := UnforcedLeray.B0296.ae_kernelAbs_lt_top'
    hc (UnforcedLeray.B0296.measurable_gradKernelAbs θ)
    (UnforcedLeray.B0296.gradKernelAbs_ne_top θ) hkernelMass hper₁ hT₁m
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) ENNReal.ofNat_ne_top hT₁.eLpNorm_ne_top
  have hfinite₂ := UnforcedLeray.B0296.ae_kernelAbs_lt_top'
    hc (UnforcedLeray.B0296.measurable_gradKernelAbs θ)
    (UnforcedLeray.B0296.gradKernelAbs_ne_top θ) hkernelMass hper₂ hT₂m
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) ENNReal.ofNat_ne_top hT₂.eLpNorm_ne_top
  have hfiniteSum := UnforcedLeray.B0296.ae_kernelAbs_lt_top'
    hc (UnforcedLeray.B0296.measurable_gradKernelAbs θ)
    (UnforcedLeray.B0296.gradKernelAbs_ne_top θ) hkernelMass hperSum hTsumM
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) ENNReal.ofNat_ne_top hTsum.eLpNorm_ne_top
  filter_upwards [hfinite₁, hfinite₂, hfiniteSum] with z hz₁ hz₂ hzSum
  have hInt₁ : Integrable
      (fun w : Plane => UnforcedLeray.B0296.divKernel θ w (T₁ (z - w))) :=
    UnforcedLeray.B0296.integrable_kconv_of_lt_top
      (A := UnforcedLeray.B0296.divKernel θ)
      (k := UnforcedLeray.B0296.gradKernelAbs θ)
      (UnforcedLeray.B0296.enorm_divKernel_le θ) z
      (UnforcedLeray.B0296.aestronglyMeasurable_divIntegrand θ hT₁m z) hz₁
  have hInt₂ : Integrable
      (fun w : Plane => UnforcedLeray.B0296.divKernel θ w (T₂ (z - w))) :=
    UnforcedLeray.B0296.integrable_kconv_of_lt_top
      (A := UnforcedLeray.B0296.divKernel θ)
      (k := UnforcedLeray.B0296.gradKernelAbs θ)
      (UnforcedLeray.B0296.enorm_divKernel_le θ) z
      (UnforcedLeray.B0296.aestronglyMeasurable_divIntegrand θ hT₂m z) hz₂
  have hIntSum : Integrable
      (fun w : Plane => UnforcedLeray.B0296.divKernel θ w ((T₁ + T₂) (z - w))) :=
    UnforcedLeray.B0296.integrable_kconv_of_lt_top
      (A := UnforcedLeray.B0296.divKernel θ)
      (k := UnforcedLeray.B0296.gradKernelAbs θ)
      (UnforcedLeray.B0296.enorm_divKernel_le θ) z
      (UnforcedLeray.B0296.aestronglyMeasurable_divIntegrand θ hTsumM z) hzSum
  rw [UnforcedLeray.B0296.heatDiv_apply_of_pos hθ,
    UnforcedLeray.B0296.heatDiv_apply_of_pos hθ,
    UnforcedLeray.B0296.heatDiv_apply_of_pos hθ]
  calc
    (∫ w : Plane, UnforcedLeray.B0296.divKernel θ w
        ((fun z => T₁ z + T₂ z) (z - w))) =
        ∫ w : Plane, UnforcedLeray.B0296.divKernel θ w (T₁ (z - w)) +
          UnforcedLeray.B0296.divKernel θ w (T₂ (z - w)) := by
      exact integral_congr_ae (Filter.Eventually.of_forall fun w => by
        change UnforcedLeray.B0296.divKernel θ w
          (T₁ (z - w) + T₂ (z - w)) = _
        exact divKernel_add θ w _ _)
    _ = (∫ w : Plane, UnforcedLeray.B0296.divKernel θ w (T₁ (z - w))) +
        ∫ w : Plane, UnforcedLeray.B0296.divKernel θ w (T₂ (z - w)) :=
      integral_add hInt₁ hInt₂

end UnforcedLeray.HeatCylinder

#print axioms UnforcedLeray.HeatCylinder.heatDiv_translate
#print axioms UnforcedLeray.HeatCylinder.heatDiv_smul_ae
#print axioms UnforcedLeray.HeatCylinder.heatDiv_add_ae
