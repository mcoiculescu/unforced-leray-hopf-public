import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.AxialHeatCommutatorAE
import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.AxialWeightDifference

/-!
# Pointwise kernel control for the actual weighted heat commutator

The exact commutator identity is now dominated by a scalar Gaussian kernel times the weighted
input column. The multiplier is an explicit polynomial in the axial shift; its Gaussian mass is
the remaining age-zero continuity estimate.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.B0579 hiding Plane

/-- The nonnegative axial ratio modulus appearing in the arbitrary-shift comparison. -/
def axialWeightDifferenceModulus (m : ℝ) (w : Plane) : ℝ :=
  ((1 + 2 * |w.2| + |w.2| ^ 2) ^ (m / 2)) ^ 2 - 1

theorem axialWeightDifferenceModulus_nonneg {m : ℝ} (hm : 0 ≤ m) (w : Plane) :
    0 ≤ axialWeightDifferenceModulus m w := by
  have hb : 1 ≤ 1 + 2 * |w.2| + |w.2| ^ 2 := by
    nlinarith [abs_nonneg w.2, sq_nonneg |w.2|]
  have hr := Real.one_le_rpow hb (by linarith : 0 ≤ m / 2)
  dsimp [axialWeightDifferenceModulus]
  nlinarith [sq_nonneg ((1 + 2 * |w.2| + |w.2| ^ 2) ^ (m / 2) - 1)]

/-- The scalar kernel governing the commutator after conjugating by the axial weight. -/
def axialHeatCommutatorKernel (θ m : ℝ) (w : Plane) : ℝ≥0∞ :=
  ENNReal.ofReal (B0284.heatKernel2 θ w * axialWeightDifferenceModulus m w)

theorem measurable_axialHeatCommutatorKernel {θ m : ℝ} :
    Measurable (axialHeatCommutatorKernel θ m) := by
  apply ENNReal.measurable_ofReal.comp
  apply (B0284.measurable_heatKernel2_right θ).mul
  unfold axialWeightDifferenceModulus
  fun_prop

/-- Pointwise, the literal Gaussian commutator integrand is bounded by the weighted input column
times the explicit scalar kernel. No representative or pointwise regularity of the `X_m` input is
used. -/
theorem axialHeatCommutator_integrand_norm_le {c m θ : ℝ} (hc : 0 < c)
    (hm : 1 ≤ m) (hθ : 0 < θ) (f : X c m) (z w : Plane) :
    ‖B0284.heatKernel2 θ w •
        ((axialWeight m z - axialWeight m (z - w)) •
          xColumnHeatLift hc f (z - w))‖ ≤
      (B0284.heatKernel2 θ w * axialWeightDifferenceModulus m w) *
        ‖axialWeight m (z - w) • xColumnHeatLift hc f (z - w)‖ := by
  have hweight := axialWeight_sub_le_shift_modulus_all
    (m := m) (by linarith : 0 ≤ m) (x := z) (w := w)
  have hA : 0 ≤ axialWeight m (z - w) := by
    dsimp [axialWeight, axialBracket]
    positivity
  have hK : 0 ≤ B0284.heatKernel2 θ w := B0284.heatKernel2_nonneg hθ w
  have hM : 0 ≤ axialWeightDifferenceModulus m w :=
    axialWeightDifferenceModulus_nonneg (by linarith : 0 ≤ m) w
  have hfactor :
      |axialWeight m z - axialWeight m (z - w)| ≤
        axialWeightDifferenceModulus m w * axialWeight m (z - w) := by
    simpa [axialWeightDifferenceModulus] using hweight
  have hweightedNorm :
      ‖axialWeight m (z - w) • xColumnHeatLift hc f (z - w)‖ =
        axialWeight m (z - w) * ‖xColumnHeatLift hc f (z - w)‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hA]
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hK, norm_smul, Real.norm_eq_abs,
    hweightedNorm]
  calc
    B0284.heatKernel2 θ w *
        (|axialWeight m z - axialWeight m (z - w)| *
          ‖xColumnHeatLift hc f (z - w)‖) ≤
      B0284.heatKernel2 θ w *
        (axialWeightDifferenceModulus m w * axialWeight m (z - w) *
          ‖xColumnHeatLift hc f (z - w)‖) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hfactor (norm_nonneg _)) hK
    _ = (B0284.heatKernel2 θ w * axialWeightDifferenceModulus m w) *
        (axialWeight m (z - w) * ‖xColumnHeatLift hc f (z - w)‖) := by ring

/-- The literal commutator at a.e. points of the normalized periodic cell is dominated by the
positive convolution of its actual weighted input with `axialHeatCommutatorKernel`. -/
theorem axialHeatCommutator_norm_le_kernel {c m θ : ℝ} (hc : 0 < c)
    (hm : 1 ≤ m) (hθ : 0 < θ) (f : X c m) :
    ∀ᵐ z ∂(B0284.cellMeasure c),
      ‖axialWeight m z • B0284.heat θ (xColumnHeatLift hc f) z -
          B0284.heat θ (fun x => axialWeight m x • xColumnHeatLift hc f x) z‖ₑ ≤
        ∫⁻ w : Plane, axialHeatCommutatorKernel θ m w *
          ‖axialWeight m (z - w) • xColumnHeatLift hc f (z - w)‖ₑ := by
  have hcomm := axialHeatCommutator_ae hc hm hθ f
  filter_upwards [hcomm] with z hz
  rw [hz]
  calc
    ‖∫ w : Plane, B0284.heatKernel2 θ w •
        ((axialWeight m z - axialWeight m (z - w)) •
          xColumnHeatLift hc f (z - w))‖ₑ ≤
        ∫⁻ w : Plane, ‖B0284.heatKernel2 θ w •
          ((axialWeight m z - axialWeight m (z - w)) •
            xColumnHeatLift hc f (z - w))‖ₑ := enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ w : Plane, axialHeatCommutatorKernel θ m w *
        ‖axialWeight m (z - w) • xColumnHeatLift hc f (z - w)‖ₑ := by
          apply lintegral_mono
          intro w
          have hpoint := axialHeatCommutator_integrand_norm_le hc hm hθ f z w
          have hcoeff : 0 ≤ B0284.heatKernel2 θ w * axialWeightDifferenceModulus m w :=
            mul_nonneg (B0284.heatKernel2_nonneg hθ w)
              (axialWeightDifferenceModulus_nonneg (by linarith : 0 ≤ m) w)
          calc
            ‖B0284.heatKernel2 θ w •
                ((axialWeight m z - axialWeight m (z - w)) •
                  xColumnHeatLift hc f (z - w))‖ₑ =
                ENNReal.ofReal ‖B0284.heatKernel2 θ w •
                  ((axialWeight m z - axialWeight m (z - w)) •
                    xColumnHeatLift hc f (z - w))‖ := by rw [← ofReal_norm]
            _ ≤ ENNReal.ofReal ((B0284.heatKernel2 θ w *
                  axialWeightDifferenceModulus m w) *
                  ‖axialWeight m (z - w) • xColumnHeatLift hc f (z - w)‖) :=
                ENNReal.ofReal_le_ofReal hpoint
            _ = axialHeatCommutatorKernel θ m w *
                ‖axialWeight m (z - w) • xColumnHeatLift hc f (z - w)‖ₑ := by
                  rw [axialHeatCommutatorKernel]
                  calc
                    ENNReal.ofReal ((B0284.heatKernel2 θ w *
                        axialWeightDifferenceModulus m w) *
                        ‖axialWeight m (z - w) • xColumnHeatLift hc f (z - w)‖) =
                        ENNReal.ofReal (B0284.heatKernel2 θ w *
                          axialWeightDifferenceModulus m w) *
                          ENNReal.ofReal ‖axialWeight m (z - w) •
                            xColumnHeatLift hc f (z - w)‖ := by
                              rw [← ENNReal.ofReal_mul hcoeff]
                    _ = ENNReal.ofReal (B0284.heatKernel2 θ w *
                          axialWeightDifferenceModulus m w) *
                          ‖axialWeight m (z - w) • xColumnHeatLift hc f (z - w)‖ₑ := by
                              rw [← ofReal_norm]

/-! The pointwise domination passes through the actual normalized-cell Young inequality. -/

theorem eLpNorm_axialHeatCommutator_le_kernel {c m θ : ℝ} (hc : 0 < c)
    (hm : 1 ≤ m) (hθ : 0 < θ) (f : X c m) :
    eLpNorm (fun z => axialWeight m z • B0284.heat θ (xColumnHeatLift hc f) z -
        B0284.heat θ (fun x => axialWeight m x • xColumnHeatLift hc f x) z)
        2 (B0284.cellMeasure c) ≤
      (∫⁻ w : Plane, axialHeatCommutatorKernel θ m w) *
        eLpNorm (fun z => axialWeight m z • xColumnHeatLift hc f z) 2
          (B0284.cellMeasure c) := by
  let g : Plane → Plane := fun z => axialWeight m z • xColumnHeatLift hc f z
  have hgmeas : Measurable g := by
    dsimp [g]
    exact (continuous_axialWeight m).measurable.smul
      (stronglyMeasurable_xColumnHeatLift hc f).measurable
  have hgper : B0284.IsQPeriodic c g := by
    intro z
    dsimp [g]
    change axialWeight m (z.1 + c, z.2) • xColumnHeatLift hc f (z.1 + c, z.2) = _
    rw [show axialWeight m (z.1 + c, z.2) = axialWeight m z by
      simp [axialWeight, axialBracket], periodic_xColumnHeatLift hc f z]
  have hdom := axialHeatCommutator_norm_le_kernel hc hm hθ f
  let G : Plane → ℝ≥0∞ := fun z => ∫⁻ w : Plane,
    axialHeatCommutatorKernel θ m w * ‖g (z - w)‖ₑ
  have hmono : eLpNorm (fun z => axialWeight m z •
        B0284.heat θ (xColumnHeatLift hc f) z - B0284.heat θ g z)
        2 (B0284.cellMeasure c) ≤ eLpNorm G 2 (B0284.cellMeasure c) := by
    refine eLpNorm_mono_enorm_ae (p := (2 : ℝ≥0∞)) ?_
    filter_upwards [hdom] with z hz
    simpa [G, enorm_eq_self] using hz
  calc
    eLpNorm (fun z => axialWeight m z •
          B0284.heat θ (xColumnHeatLift hc f) z - B0284.heat θ g z)
        2 (B0284.cellMeasure c) ≤
        eLpNorm G 2 (B0284.cellMeasure c) := hmono
    _ ≤ (∫⁻ w : Plane, axialHeatCommutatorKernel θ m w) *
        eLpNorm g 2 (B0284.cellMeasure c) :=
          B0296.eLpNorm_kernelAbs_le' hc measurable_axialHeatCommutatorKernel
            (fun w => ENNReal.ofReal_ne_top) hgper hgmeas.aestronglyMeasurable
            (by norm_num) (by norm_num)

#print axioms axialHeatCommutator_norm_le_kernel
#print axioms eLpNorm_axialHeatCommutator_le_kernel

#print axioms axialWeightDifferenceModulus_nonneg
#print axioms axialHeatCommutator_integrand_norm_le
#print axioms measurable_axialHeatCommutatorKernel

end UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution
