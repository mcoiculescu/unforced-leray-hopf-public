import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.KernelMoment
import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.WeightedKernel
import UnforcedLeray.Units.B0296.Conv
import UnforcedLeray.Lib.HeatCylinder.CellBridge

/-!
# Axially weighted periodic heat-divergence estimate

This leaf applies the actual B0296 planar heat-gradient kernel to the q-periodic cylinder.
The axial Japanese weight is separated from the periodic coordinate, so Peetre's inequality
reduces the estimate to the weighted Gaussian-gradient moment in `KernelMoment`.
-/

set_option autoImplicit false
set_option maxHeartbeats 500000

noncomputable section

namespace UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

open MeasureTheory
open scoped NNReal ENNReal
open UnforcedLeray.B0296
open UnforcedLeray.B0579
open UnforcedLeray.B0284

/-- The q-independent axial weight used in the periodic weighted Young estimate. -/
def axialWeight (m : ℝ) (z : Plane) : ℝ := axialBracket z ^ m

/-- The sign-corrected Gaussian response used for the physical B0610 source `-div F`. -/
def negativeHeatDiv (θ : ℝ) (T : Plane → Plane × Plane) : Plane → Plane :=
  fun z => -UnforcedLeray.B0296.heatDiv θ T z

theorem continuous_axialWeight (m : ℝ) : Continuous (axialWeight m) := by
  have hEq : axialWeight m = fun z : Plane => jb (0, z.2) ^ (m / 2) := by
    funext z
    rw [axialWeight, axialBracket_rpow]
    simp [jb]
  rw [hEq]
  exact (continuous_jb_rpow (m / 2)).comp (continuous_const.prodMk continuous_snd)

/-- The one-dimensional Gaussian derivative has zero signed mass; this is the kernel factor
needed when proving zero circulation of the actual heat-divergence response by Fubini. -/
theorem integral_dHeatKernel_eq_zero {θ : ℝ} (_hθ : 0 < θ) :
    ∫ x : ℝ, UnforcedLeray.B0296.dHeatKernel θ x = 0 := by
  have hodd : (fun x : ℝ => UnforcedLeray.B0296.dHeatKernel θ (-x)) =
      fun x => -UnforcedLeray.B0296.dHeatKernel θ x := by
    funext x
    simp [UnforcedLeray.B0296.dHeatKernel, UnforcedLeray.B0191.heatKernel]
    ring
  have hneg := integral_neg_eq_self
    (fun x : ℝ => UnforcedLeray.B0296.dHeatKernel θ x) (volume : Measure ℝ)
  rw [hodd, integral_neg] at hneg
  have hzero : (2 : ℝ) * (∫ x : ℝ, UnforcedLeray.B0296.dHeatKernel θ x) = 0 := by
    nlinarith [hneg]
  exact (mul_eq_zero.mp hzero).resolve_left (by norm_num)

/-- Both planar components of the actual Gaussian gradient have zero signed mass. -/
theorem integral_gradHeatKernel2_fst_eq_zero {θ : ℝ} (hθ : 0 < θ) :
    ∫ w : Plane, (UnforcedLeray.B0296.gradHeatKernel2 θ w).1 = 0 := by
  calc
    ∫ w : Plane, (UnforcedLeray.B0296.gradHeatKernel2 θ w).1 =
        (∫ x : ℝ, UnforcedLeray.B0296.dHeatKernel θ x) *
          ∫ y : ℝ, UnforcedLeray.B0191.heatKernel 1 θ y := by
      rw [show (fun w : Plane => (UnforcedLeray.B0296.gradHeatKernel2 θ w).1) =
        fun w => UnforcedLeray.B0296.dHeatKernel θ w.1 *
          UnforcedLeray.B0191.heatKernel 1 θ w.2 by rfl]
      exact integral_prod_mul _ _
    _ = 0 := by rw [integral_dHeatKernel_eq_zero hθ, zero_mul]

theorem integral_gradHeatKernel2_snd_eq_zero {θ : ℝ} (hθ : 0 < θ) :
    ∫ w : Plane, (UnforcedLeray.B0296.gradHeatKernel2 θ w).2 = 0 := by
  calc
    ∫ w : Plane, (UnforcedLeray.B0296.gradHeatKernel2 θ w).2 =
        (∫ x : ℝ, UnforcedLeray.B0191.heatKernel 1 θ x) *
          ∫ y : ℝ, UnforcedLeray.B0296.dHeatKernel θ y := by
      rw [show (fun w : Plane => (UnforcedLeray.B0296.gradHeatKernel2 θ w).2) =
        fun w => UnforcedLeray.B0191.heatKernel 1 θ w.1 *
          UnforcedLeray.B0296.dHeatKernel θ w.2 by rfl]
      exact integral_prod_mul _ _
    _ = 0 := by rw [integral_dHeatKernel_eq_zero hθ, mul_zero]

/-- ENNReal kernel for the axially weighted B0296 gradient convolution. -/
def axialGradKernel (m θ : ℝ) (w : Plane) : ℝ≥0∞ :=
  ENNReal.ofReal (2 ^ (m / 2)) *
    ENNReal.ofReal (axialWeight m w) * gradKernelAbs θ w

theorem axialGradKernel_measurable (m θ : ℝ) : Measurable (axialGradKernel m θ) := by
  unfold axialGradKernel
  exact (measurable_const.mul ((continuous_axialWeight m).measurable.ennreal_ofReal)).mul
    (measurable_gradKernelAbs θ)

theorem axialGradKernel_ne_top (m θ : ℝ) (w : Plane) : axialGradKernel m θ w ≠ ⊤ := by
  unfold axialGradKernel
  exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    ENNReal.ofReal_ne_top) (gradKernelAbs_ne_top θ w)

/-- Pointwise weight transfer through the actual B0296 divergence kernel. -/
theorem enorm_axial_weighted_divKernel_le {m θ : ℝ} (hm : 0 ≤ m) (w z : Plane)
    (T : Plane × Plane) :
    ‖axialWeight m z • divKernel θ w T‖ₑ ≤
      axialGradKernel m θ w * ‖axialWeight m (z - w) • T‖ₑ := by
  have hpeetre := axialBracket_rpow_le_peetre hm z w
  have hwz : 0 ≤ axialWeight m z := by
    dsimp [axialWeight, axialBracket]
    positivity
  have hwd : 0 ≤ axialWeight m (z - w) := by
    dsimp [axialWeight, axialBracket]
    positivity
  have hww : 0 ≤ axialWeight m w := by
    dsimp [axialWeight, axialBracket]
    positivity
  have hkernel := enorm_divKernel_le θ w T
  have hpeetreE : ENNReal.ofReal (axialWeight m z) ≤
      ENNReal.ofReal (2 ^ (m / 2)) * ENNReal.ofReal (axialWeight m (z - w)) *
        ENNReal.ofReal (axialWeight m w) := by
    calc
      ENNReal.ofReal (axialWeight m z) ≤
          ENNReal.ofReal (2 ^ (m / 2) * axialWeight m (z - w) * axialWeight m w) :=
        ENNReal.ofReal_le_ofReal (by simpa [axialWeight] using hpeetre)
      _ = ENNReal.ofReal (2 ^ (m / 2)) * ENNReal.ofReal (axialWeight m (z - w)) *
            ENNReal.ofReal (axialWeight m w) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
  rw [enorm_smul, Real.enorm_eq_ofReal_abs, abs_of_nonneg hwz,
    enorm_smul, Real.enorm_eq_ofReal_abs, abs_of_nonneg hwd]
  calc
    ENNReal.ofReal (axialWeight m z) * ‖divKernel θ w T‖ₑ ≤
        (ENNReal.ofReal (2 ^ (m / 2)) * ENNReal.ofReal (axialWeight m (z - w)) *
          ENNReal.ofReal (axialWeight m w)) * ‖divKernel θ w T‖ₑ :=
      mul_le_mul_of_nonneg_right hpeetreE (by positivity)
    _ ≤ (ENNReal.ofReal (2 ^ (m / 2)) * ENNReal.ofReal (axialWeight m (z - w)) *
          ENNReal.ofReal (axialWeight m w)) * (gradKernelAbs θ w * ‖T‖ₑ) := by
      exact mul_le_mul_of_nonneg_left hkernel (by positivity)
    _ = (ENNReal.ofReal (2 ^ (m / 2)) * ENNReal.ofReal (axialWeight m w) *
          gradKernelAbs θ w) *
        (ENNReal.ofReal (axialWeight m (z - w)) * ‖T‖ₑ) := by ring

/-- Weighted periodic Young: multiply both the input and output of the actual planar B0296
heat-divergence convolution by the axial weight. The right side is the weighted input norm
times the explicitly defined weighted gradient-kernel mass. -/
theorem eLpNorm_axialHeatDiv_le {c θ m : ℝ} (hc : 0 < c) (hθ : 0 < θ) (hm : 0 ≤ m)
    {T : Plane → Plane × Plane} (hper : IsQPeriodic c T)
    (hT : AEStronglyMeasurable T volume) {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ⊤) :
    eLpNorm (fun z => axialWeight m z • heatDiv θ T z) p (UnforcedLeray.B0284.cellMeasure c) ≤
      (∫⁻ w : Plane, axialGradKernel m θ w) *
        eLpNorm (fun z => axialWeight m z • T z) p (UnforcedLeray.B0284.cellMeasure c) := by
  have hweightedPer : IsQPeriodic c (fun z => axialWeight m z • T z) := by
    intro z
    change axialWeight m (z.1 + c, z.2) • T (z.1 + c, z.2) =
      axialWeight m z • T z
    rw [show axialWeight m (z.1 + c, z.2) = axialWeight m z by
      simp [axialWeight, axialBracket]]
    exact congrArg (fun v => axialWeight m z • v) (hper z)
  have hweightedMeas : AEStronglyMeasurable (fun z => axialWeight m z • T z) volume := by
    exact (continuous_axialWeight m).aestronglyMeasurable.smul hT
  have hbound : ∀ z, ‖axialWeight m z • heatDiv θ T z‖ₑ ≤
      ∫⁻ w : Plane, axialGradKernel m θ w *
        ‖(fun x => axialWeight m x • T x) (z - w)‖ₑ := by
    intro z
    rw [heatDiv_apply_of_pos hθ]
    calc
      ‖axialWeight m z • ∫ w : Plane, divKernel θ w (T (z - w))‖ₑ ≤
          ∫⁻ w : Plane, ‖axialWeight m z • divKernel θ w (T (z - w))‖ₑ :=
            by
              rw [← integral_smul]
              exact enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ w : Plane, axialGradKernel m θ w *
          ‖axialWeight m (z - w) • T (z - w)‖ₑ := by
            refine lintegral_mono fun w => ?_
            exact enorm_axial_weighted_divKernel_le hm w z (T (z - w))
  calc
    eLpNorm (fun z => axialWeight m z • heatDiv θ T z) p
        (UnforcedLeray.B0284.cellMeasure c) ≤
        eLpNorm (fun z => ∫⁻ w : Plane, axialGradKernel m θ w *
          ‖(fun x => axialWeight m x • T x) (z - w)‖ₑ) p
          (UnforcedLeray.B0284.cellMeasure c) :=
      eLpNorm_mono_enorm (fun z => hbound z)
    _ ≤ (∫⁻ w : Plane, axialGradKernel m θ w) *
        eLpNorm (fun z => axialWeight m z • T z) p
          (UnforcedLeray.B0284.cellMeasure c) := by
      exact eLpNorm_kernelAbs_le' hc (axialGradKernel_measurable m θ)
        (axialGradKernel_ne_top m θ) hweightedPer hweightedMeas hp hp'

/-- The ENNReal mass of the axial weighted gradient kernel is bounded by the actual
unit-age Gaussian moment times `θ^(-1/2)`. This constant is independent of the cylinder
period `c`; it is the heat supplier bound needed by fixed-parameter strip evolution. -/
theorem axialGradKernel_lintegral_le {θ m : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hm : 0 ≤ m) :
    ∫⁻ w : Plane, axialGradKernel m θ w ≤
      ENNReal.ofReal (2 ^ (m / 2) * θ ^ (-(1 / 2 : ℝ)) *
        ∫ w : Plane, gradKernelAxialMomentDensity 1 m w) := by
  let D := gradKernelAxialMomentDensity θ m
  let D₁ := gradKernelAxialMomentDensity 1 m
  have hD : Integrable D := by
    have h := integrable_gradKernelNorm_mul_axialWeight hθ hm
    convert h using 1 <;> ext w <;> simp [D, gradKernelAxialMomentDensity, Real.norm_eq_abs]
  have hD₁ : Integrable D₁ := by
    have h := integrable_gradKernelNorm_mul_axialWeight one_pos hm
    convert h using 1 <;> ext w <;> simp [D₁, gradKernelAxialMomentDensity, Real.norm_eq_abs]
  have hD_nonneg : ∀ w, 0 ≤ D w := by
    intro w
    dsimp [D, gradKernelAxialMomentDensity]
    positivity
  have hD₁_nonneg : ∀ w, 0 ≤ D₁ w := by
    intro w
    dsimp [D₁, gradKernelAxialMomentDensity]
    positivity
  have hpoint : ∀ w, axialGradKernel m θ w =
      ENNReal.ofReal (2 ^ (m / 2) * D w) := by
    intro w
    have hW : 0 ≤ axialWeight m w := by
      dsimp [axialWeight, axialBracket]
      positivity
    have hCax : 0 ≤ (2 : ℝ) ^ (m / 2) * axialWeight m w :=
      mul_nonneg (Real.rpow_nonneg (by norm_num) _) hW
    rw [axialGradKernel, gradKernelAbs,
      Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs,
      ← ENNReal.ofReal_add (abs_nonneg ((gradHeatKernel2 θ w).1))
        (abs_nonneg ((gradHeatKernel2 θ w).2)),
      ← ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _),
      ← ENNReal.ofReal_mul hCax]
    congr 1
    simp only [D, gradKernelAxialMomentDensity, axialWeight, axialBracket_rpow,
      Real.norm_eq_abs]
    ring
  have hmass : ∫⁻ w : Plane, axialGradKernel m θ w =
      ENNReal.ofReal (2 ^ (m / 2) * ∫ w : Plane, D w) := by
    rw [show (fun w : Plane => axialGradKernel m θ w) =
      (fun w => ENNReal.ofReal (2 ^ (m / 2) * D w)) by funext w; exact hpoint w]
    rw [← ofReal_integral_eq_lintegral_ofReal (hD.const_mul (2 ^ (m / 2)))
      (Filter.Eventually.of_forall fun w => mul_nonneg (by positivity) (hD_nonneg w))]
    rw [integral_const_mul]
  have hmoment := integral_gradKernelAxialMoment_le hθ hθ1 hm
  rw [hmass]
  simp only [D]
  apply ENNReal.ofReal_le_ofReal
  have hC : 0 ≤ (2 : ℝ) ^ (m / 2) := by positivity
  calc
    2 ^ (m / 2 : ℝ) * ∫ w : Plane, gradKernelAxialMomentDensity θ m w ≤
        2 ^ (m / 2 : ℝ) *
          (θ ^ (-(1 / 2 : ℝ)) * ∫ w : Plane,
            gradKernelAxialMomentDensity 1 m w) :=
      mul_le_mul_of_nonneg_left hmoment hC
    _ = 2 ^ (m / 2 : ℝ) * θ ^ (-(1 / 2 : ℝ)) *
        ∫ w : Plane, gradKernelAxialMomentDensity 1 m w := by ring

/-- Actual B0296 weighted heat-divergence smoothing with its explicit, cylinder-independent
moment constant. The input/output here are the axial-weighted periodic tensor and field; the
centered-cell comparison to the radial B0579 `X c m` norm is a separate finite-cylinder step. -/
theorem eLpNorm_axialHeatDiv_smoothing {c θ m : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    (hθ1 : θ ≤ 1) (hm : 0 ≤ m) {T : Plane → Plane × Plane}
    (hper : IsQPeriodic c T) (hT : AEStronglyMeasurable T volume)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ⊤) :
    eLpNorm (fun z => axialWeight m z • heatDiv θ T z) p
        (UnforcedLeray.B0284.cellMeasure c) ≤
      ENNReal.ofReal (2 ^ (m / 2) * θ ^ (-(1 / 2 : ℝ)) *
        ∫ w : Plane, gradKernelAxialMomentDensity 1 m w) *
        eLpNorm (fun z => axialWeight m z • T z) p
          (UnforcedLeray.B0284.cellMeasure c) := by
  calc
    _ ≤ (∫⁻ w : Plane, axialGradKernel m θ w) *
        eLpNorm (fun z => axialWeight m z • T z) p
          (UnforcedLeray.B0284.cellMeasure c) :=
      eLpNorm_axialHeatDiv_le hc hθ hm hper hT hp hp'
    _ ≤ _ := by
      exact mul_le_mul_of_nonneg_right (axialGradKernel_lintegral_le hθ hθ1 hm)
        (by positivity)

/-- Convolution with the actual B0296 gradient kernel has a measurable pointwise representative
even when its input is given only as an almost-everywhere strongly measurable function. The
integral is unchanged at each output point after replacing the input by its strongly measurable
representative, since translations preserve volume-null sets. -/
theorem measurable_heatDiv_of_aestronglyMeasurable {θ : ℝ} {T : Plane → Plane × Plane}
    (hT : AEStronglyMeasurable T volume) : Measurable (heatDiv θ T) := by
  let Tsm := hT.mk T
  have hTsm : StronglyMeasurable Tsm := hT.stronglyMeasurable_mk
  have hTae : T =ᵐ[volume] Tsm := hT.ae_eq_mk
  have hsub : Measurable (fun q : Plane × Plane => q.1 - q.2) :=
    measurable_fst.sub measurable_snd
  have hshift : StronglyMeasurable (fun q : Plane × Plane => Tsm (q.1 - q.2)) :=
    hTsm.comp_measurable hsub
  have hkernel : StronglyMeasurable
      (fun q : Plane × Plane => divKernel θ q.2 (Tsm (q.1 - q.2))) := by
    change StronglyMeasurable (fun q : Plane × Plane =>
      (gradHeatKernel2 θ q.2).1 • (Tsm (q.1 - q.2)).1 +
        (gradHeatKernel2 θ q.2).2 • (Tsm (q.1 - q.2)).2)
    exact (((measurable_gradHeatKernel2_fst θ).comp measurable_snd).stronglyMeasurable.smul
      hshift.fst).add (((measurable_gradHeatKernel2_snd θ).comp measurable_snd).stronglyMeasurable.smul
      hshift.snd)
  have hInt : Measurable (fun z : Plane =>
      ∫ w : Plane, divKernel θ w (Tsm (z - w))) :=
    hkernel.integral_prod_right'.measurable
  by_cases hθ : 0 < θ
  · have hEq : heatDiv θ T = fun z => ∫ w : Plane, divKernel θ w (Tsm (z - w)) := by
      funext z
      rw [heatDiv_apply_of_pos hθ]
      have hshiftAE : (fun w : Plane => T (z - w)) =ᵐ[volume]
          fun w => Tsm (z - w) := by
        have h' := (quasiMeasurePreserving_sub_left_of_right_invariant
          (volume : Measure Plane) z).ae hTae
        filter_upwards [h'] with w hw
        exact hw
      exact integral_congr_ae (hshiftAE.mono fun w hw =>
        congrArg (divKernel θ w) hw)
    rw [hEq]
    exact hInt
  · have hz : heatDiv θ T = 0 := by
      funext z
      simp [heatDiv, hθ]
    rw [hz]
    exact measurable_const

/-- The weighted periodic heat-divergence field is an actual `L²` function whenever the
axially weighted periodic input tensor is in `L²`; this packages the measurability and finite
kernel-moment estimate needed before passing to the physical zero-circulation subspace. -/
theorem memLp_axialHeatDiv {c θ m : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    (hθ1 : θ ≤ 1) (hm : 0 ≤ m) {T : Plane → Plane × Plane}
    (hper : IsQPeriodic c T) (hT : AEStronglyMeasurable T volume)
    (hfin : eLpNorm (fun z => axialWeight m z • T z) 2
      (UnforcedLeray.B0284.cellMeasure c) ≠ ⊤) :
    MemLp (fun z => axialWeight m z • heatDiv θ T z) 2
      (UnforcedLeray.B0284.cellMeasure c) := by
  refine ⟨?_, ?_⟩
  · have hheat : AEStronglyMeasurable (heatDiv θ T)
        (UnforcedLeray.B0284.cellMeasure c) := by
      rw [heatDiv_eq_integral hθ]
      exact aestronglyMeasurable_kconv c (divKernel θ)
        (aestronglyMeasurable_divIntegrand_prod θ hT)
    exact (continuous_axialWeight m).aestronglyMeasurable.smul hheat
  · have hbound := eLpNorm_axialHeatDiv_smoothing hc hθ hθ1 hm hper hT
      (by norm_num : 1 ≤ (2 : ℝ≥0∞)) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
    have hcoef : ENNReal.ofReal (2 ^ (m / 2) * θ ^ (-(1 / 2 : ℝ)) *
        ∫ w : Plane, gradKernelAxialMomentDensity 1 m w) < ⊤ := ENNReal.ofReal_lt_top
    exact hbound.trans_lt (ENNReal.mul_lt_top hcoef hfin.lt_top)

/-- The first scalar component of the actual heat-divergence output belongs to B0579's radial
`X c m` whenever the axial weighted periodic input is square integrable. The normalization
transfer is the existing HeatCylinder cell bridge; the only extra field is measurability of the
actual heat output, needed to identify its centered-cell representative. -/
theorem memLp_heatDiv_fst_X {c θ m : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    (hθ1 : θ ≤ 1) (hm : 0 ≤ m) {T : Plane → Plane × Plane}
    (hper : IsQPeriodic c T) (hT : AEStronglyMeasurable T volume)
    (hfin : eLpNorm (fun z => axialWeight m z • T z) 2
      (UnforcedLeray.B0284.cellMeasure c) ≠ ⊤) :
    MemLp (fun z => (heatDiv θ T z).1) 2 (UnforcedLeray.B0579.cellMeasure c m) := by
  let f := fun z : Plane => axialWeight m z • heatDiv θ T z
  have hfmeas : Measurable f := by
    exact (continuous_axialWeight m).measurable.smul
      (measurable_heatDiv_of_aestronglyMeasurable hT)
  have hfper : IsQPeriodic c f := by
    intro z
    change axialWeight m (z.1 + c, z.2) • heatDiv θ T (z.1 + c, z.2) =
      axialWeight m z • heatDiv θ T z
    rw [show axialWeight m (z.1 + c, z.2) = axialWeight m z by
      simp [axialWeight, axialBracket], UnforcedLeray.B0296.heatDiv_periodic hper z]
  have hfB : MemLp f 2 (UnforcedLeray.B0284.cellMeasure c) := by
    simpa [f] using memLp_axialHeatDiv hc hθ hθ1 hm hper hT hfin
  have hfCyl : MemLp f 2 (UnforcedLeray.Cyl.cellμ c) :=
    UnforcedLeray.HeatCylinder.memLp_cyl_of_memLp_cellMeasure hc hfmeas hfper hfB
  have hfst : MemLp (fun z => (f z).1) 2 (UnforcedLeray.Cyl.cellμ c) := by
    refine hfCyl.of_le (continuous_fst.comp_aestronglyMeasurable hfCyl.1) ?_
    filter_upwards [] with z
    exact norm_fst_le (f z)
  let Cc : ℝ := (1 + c ^ 2 / 4) ^ (m / 2)
  have hCc : 0 ≤ Cc := by dsimp [Cc]; positivity
  have hrad : MemLp (fun z => UnforcedLeray.B0579.bracket z ^ m * (heatDiv θ T z).1)
      2 (UnforcedLeray.Cyl.cellμ c) := by
    refine (hfst.const_mul Cc).of_le
      ((UnforcedLeray.B0579.continuous_bracket_rpow m).aestronglyMeasurable.mul
        (continuous_fst.comp_aestronglyMeasurable
          ((measurable_heatDiv_of_aestronglyMeasurable hT).aestronglyMeasurable.mono_ac
            Measure.absolutelyContinuous_restrict))) ?_
    filter_upwards [ae_restrict_mem (UnforcedLeray.Cyl.measurableSet_cell c)] with z hz
    have hz' : z ∈ UnforcedLeray.B0579.cell c := by
      simp only [UnforcedLeray.Cyl.cell, Set.mem_prod, Set.mem_Ico, Set.mem_univ] at hz
      simp only [UnforcedLeray.B0579.cell, Set.mem_prod, Set.mem_Ico, Set.mem_univ]
      exact ⟨⟨by linarith [hz.1.1], hz.1.2⟩, trivial⟩
    have hw := bracket_le_centered_axial hc hm hz'
    have hax : 0 ≤ axialWeight m z := by
      dsimp [axialWeight, axialBracket]
      positivity
    have hradw : 0 ≤ UnforcedLeray.B0579.bracket z ^ m :=
      (UnforcedLeray.B0579.bracket_rpow_pos m z).le
    have hcoord : (f z).1 = axialWeight m z * (heatDiv θ T z).1 := by
      simp [f, axialWeight, smul_eq_mul]
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_nonneg hradw]
    calc
      UnforcedLeray.B0579.bracket z ^ m * |(heatDiv θ T z).1| ≤
          Cc * axialWeight m z * |(heatDiv θ T z).1| :=
        mul_le_mul_of_nonneg_right hw (abs_nonneg ((heatDiv θ T z).1))
      _ = |Cc * (f z).1| := by
        rw [hcoord, abs_mul, abs_of_nonneg hCc, abs_mul, abs_of_nonneg hax]
        ring
  have hrad' : MemLp (fun z => UnforcedLeray.B0579.bracket z ^ m *
      (heatDiv θ T z).1) 2 (volume.restrict (UnforcedLeray.B0579.cell c)) := by
    have hcell : UnforcedLeray.Cyl.cell c = UnforcedLeray.B0579.cell c := by
      simp only [UnforcedLeray.Cyl.cell, UnforcedLeray.B0579.cell]
      congr 1
      ring
    simpa [UnforcedLeray.Cyl.cellμ, hcell] using hrad
  exact (UnforcedLeray.B0579.memLp_cellMeasure_iff c m).2 hrad'

/-- The actual heat-divergence first component maps a radial weighted tensor on the centered
cell into radial `X c m`. The proof first weakens the full radial input weight to the axial
weight, transfers that periodic class to B0284's normalized cell, and then uses the explicit
Gaussian-gradient estimate. -/
theorem memLp_heatDiv_fst_X_of_radialInput {c θ m : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    (hθ1 : θ ≤ 1) (hm : 0 ≤ m) {T : Plane → Plane × Plane}
    (hper : IsQPeriodic c T) (hT : Measurable T)
    (hRad : MemLp (fun z => UnforcedLeray.B0579.bracket z ^ m • T z) 2
      (UnforcedLeray.Cyl.cellμ c)) :
    MemLp (fun z => (heatDiv θ T z).1) 2 (UnforcedLeray.B0579.cellMeasure c m) := by
  have hAxial : MemLp (fun z => axialWeight m z • T z) 2
      (UnforcedLeray.Cyl.cellμ c) := by
    refine hRad.of_le ((continuous_axialWeight m).aestronglyMeasurable.smul
      (hT.aestronglyMeasurable.mono_ac Measure.absolutelyContinuous_restrict)) ?_
    filter_upwards [ae_restrict_mem (UnforcedLeray.Cyl.measurableSet_cell c)] with z hz
    have hz' : z ∈ UnforcedLeray.B0579.cell c := by
      simp only [UnforcedLeray.Cyl.cell, Set.mem_prod, Set.mem_Ico, Set.mem_univ] at hz
      simp only [UnforcedLeray.B0579.cell, Set.mem_prod, Set.mem_Ico, Set.mem_univ]
      exact ⟨⟨by linarith [hz.1.1], hz.1.2⟩, trivial⟩
    have hweight := axialBracket_rpow_le_bracket hm z
    have hax : 0 ≤ axialWeight m z := by
      dsimp [axialWeight, axialBracket]
      positivity
    have hrad : 0 ≤ UnforcedLeray.B0579.bracket z ^ m :=
      (UnforcedLeray.B0579.bracket_rpow_pos m z).le
    simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hax, abs_of_nonneg hrad]
    exact mul_le_mul_of_nonneg_right hweight (norm_nonneg (T z))
  have hAxialMeas : Measurable (fun z => axialWeight m z • T z) :=
    (continuous_axialWeight m).measurable.smul hT
  have hAxialPer : IsQPeriodic c (fun z => axialWeight m z • T z) := by
    intro z
    change axialWeight m (z.1 + c, z.2) • T (z.1 + c, z.2) = _
    rw [show axialWeight m (z.1 + c, z.2) = axialWeight m z by
      simp [axialWeight, axialBracket], hper z]
  have hAxialNorm := UnforcedLeray.HeatCylinder.memLp_cellMeasure_of_memLp_cyl
    hc hAxialMeas hAxialPer hAxial
  have hfin : eLpNorm (fun z => axialWeight m z • T z) 2
      (UnforcedLeray.B0284.cellMeasure c) ≠ ⊤ := hAxialNorm.eLpNorm_ne_top
  exact memLp_heatDiv_fst_X hc hθ hθ1 hm hper hT.aestronglyMeasurable hfin

/-- Quantitative centered-cell comparison of the actual radial output component to the axial
weighted full-vector output. The sole cylinder loss is the explicit factor
`(1+c^2/4)^(m/2)`. -/
theorem eLpNorm_radialHeatDiv_fst_le_axialCyl {c θ m : ℝ} (hc : 0 < c)
    (hm : 0 ≤ m) {T : Plane → Plane × Plane} :
    eLpNorm (fun z => UnforcedLeray.B0579.bracket z ^ m * (heatDiv θ T z).1) 2
        (UnforcedLeray.Cyl.cellμ c) ≤
      ENNReal.ofReal ((1 + c ^ 2 / 4) ^ (m / 2)) *
        eLpNorm (fun z => ‖axialWeight m z • heatDiv θ T z‖) 2
          (UnforcedLeray.Cyl.cellμ c) := by
  let Cc : ℝ := (1 + c ^ 2 / 4) ^ (m / 2)
  have hCc : 0 ≤ Cc := by dsimp [Cc]; positivity
  have hPoint : ∀ᵐ z ∂UnforcedLeray.Cyl.cellμ c,
      ‖UnforcedLeray.B0579.bracket z ^ m * (heatDiv θ T z).1‖ₑ ≤
        ‖Cc * ‖axialWeight m z • heatDiv θ T z‖‖ₑ := by
    filter_upwards [ae_restrict_mem (UnforcedLeray.Cyl.measurableSet_cell c)] with z hz
    have hz' : z ∈ UnforcedLeray.B0579.cell c := by
      simp only [UnforcedLeray.Cyl.cell, Set.mem_prod, Set.mem_Ico, Set.mem_univ] at hz
      simp only [UnforcedLeray.B0579.cell, Set.mem_prod, Set.mem_Ico, Set.mem_univ]
      exact ⟨⟨by linarith [hz.1.1], hz.1.2⟩, trivial⟩
    have hweight := bracket_le_centered_axial hc hm hz'
    have hax : 0 ≤ axialWeight m z := by
      dsimp [axialWeight, axialBracket]
      positivity
    have hrad : 0 ≤ UnforcedLeray.B0579.bracket z ^ m :=
      (UnforcedLeray.B0579.bracket_rpow_pos m z).le
    have hreal : |UnforcedLeray.B0579.bracket z ^ m * (heatDiv θ T z).1| ≤
        Cc * ‖axialWeight m z • heatDiv θ T z‖ := by
      rw [abs_mul, abs_of_nonneg hrad]
      calc
        UnforcedLeray.B0579.bracket z ^ m * |(heatDiv θ T z).1| ≤
            Cc * axialWeight m z * |(heatDiv θ T z).1| :=
          mul_le_mul_of_nonneg_right hweight (abs_nonneg _)
        _ ≤ Cc * ‖axialWeight m z • heatDiv θ T z‖ := by
          calc
            Cc * axialWeight m z * |(heatDiv θ T z).1| =
                Cc * (axialWeight m z * |(heatDiv θ T z).1|) := by ring
            _ ≤ Cc * (axialWeight m z * ‖heatDiv θ T z‖) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left (norm_fst_le (heatDiv θ T z)) hax) hCc
            _ = Cc * ‖axialWeight m z • heatDiv θ T z‖ := by
              rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hax]
    rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs,
      abs_of_nonneg (mul_nonneg hCc (norm_nonneg _))]
    exact ENNReal.ofReal_le_ofReal hreal
  calc
    eLpNorm (fun z => UnforcedLeray.B0579.bracket z ^ m * (heatDiv θ T z).1) 2
        (UnforcedLeray.Cyl.cellμ c) ≤
      eLpNorm (fun z => Cc * ‖axialWeight m z • heatDiv θ T z‖) 2
        (UnforcedLeray.Cyl.cellμ c) := eLpNorm_mono_enorm_ae hPoint
    _ = ENNReal.ofReal Cc *
        eLpNorm (fun z => ‖axialWeight m z • heatDiv θ T z‖) 2
          (UnforcedLeray.Cyl.cellμ c) := by
      rw [show (fun z => Cc * ‖axialWeight m z • heatDiv θ T z‖) =
        fun z => Cc • ‖axialWeight m z • heatDiv θ T z‖ by
          funext z; simp [smul_eq_mul]]
      change eLpNorm (Cc • (fun z => ‖axialWeight m z • heatDiv θ T z‖)) 2 _ = _
      rw [eLpNorm_const_smul, eLpNorm_norm, Real.enorm_of_nonneg hCc]

/-- Squared quantitative radial `X_m` output bound for the actual Gaussian heat-divergence
kernel. The centered-cell comparison contributes `(1+c²/4)^(m/2)`, while conversion from the
normalized periodic cell contributes the explicit factor `c`; the remaining age singularity is
exactly the Gaussian moment `θ^(-1/2)`. -/
theorem eLpNorm_radialHeatDiv_fst_sq_le {c θ m : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    (hθ1 : θ ≤ 1) (hm : 0 ≤ m) {T : Plane → Plane × Plane}
    (hper : IsQPeriodic c T) (hT : AEStronglyMeasurable T volume) :
    (eLpNorm (fun z => UnforcedLeray.B0579.bracket z ^ m * (heatDiv θ T z).1) 2
      (UnforcedLeray.Cyl.cellμ c)) ^ 2 ≤
      (ENNReal.ofReal ((1 + c ^ 2 / 4) ^ (m / 2))) ^ 2 * ENNReal.ofReal c *
        (ENNReal.ofReal (2 ^ (m / 2) * θ ^ (-(1 / 2 : ℝ)) *
          ∫ w : Plane, gradKernelAxialMomentDensity 1 m w) *
          eLpNorm (fun z => axialWeight m z • T z) 2
            (UnforcedLeray.B0284.cellMeasure c)) ^ 2 := by
  let f := fun z : Plane => axialWeight m z • heatDiv θ T z
  have hfmeas : Measurable f := by
    exact (continuous_axialWeight m).measurable.smul
      (measurable_heatDiv_of_aestronglyMeasurable hT)
  have hfper : IsQPeriodic c f := by
    intro z
    change axialWeight m (z.1 + c, z.2) • heatDiv θ T (z.1 + c, z.2) = _
    rw [show axialWeight m (z.1 + c, z.2) = axialWeight m z by
      simp [axialWeight, axialBracket], UnforcedLeray.B0296.heatDiv_periodic hper z]
  have hcell := UnforcedLeray.HeatCylinder.eLpNorm_sq_cyl_eq_cellMeasure hc hfmeas hfper
  have hrad := eLpNorm_radialHeatDiv_fst_le_axialCyl (θ := θ) (T := T) hc hm
  have hsm := eLpNorm_axialHeatDiv_smoothing hc hθ hθ1 hm hper hT
    (by norm_num : 1 ≤ (2 : ℝ≥0∞)) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  calc
    _ ≤ (ENNReal.ofReal ((1 + c ^ 2 / 4) ^ (m / 2)) *
        eLpNorm (fun z => ‖f z‖) 2 (UnforcedLeray.Cyl.cellμ c)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hrad 2
    _ = (ENNReal.ofReal ((1 + c ^ 2 / 4) ^ (m / 2))) ^ 2 *
        (ENNReal.ofReal c * (eLpNorm f 2
          (UnforcedLeray.B0284.cellMeasure c)) ^ 2) := by
      rw [mul_pow, eLpNorm_norm, hcell]
    _ ≤ (ENNReal.ofReal ((1 + c ^ 2 / 4) ^ (m / 2))) ^ 2 * ENNReal.ofReal c *
        (ENNReal.ofReal (2 ^ (m / 2) * θ ^ (-(1 / 2 : ℝ)) *
          ∫ w : Plane, gradKernelAxialMomentDensity 1 m w) *
          eLpNorm (fun z => axialWeight m z • T z) 2
            (UnforcedLeray.B0284.cellMeasure c)) ^ 2 := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by positivity) hsm 2)
          (ENNReal.ofReal_pos.mpr hc).le)
        (by positivity)

/-- Full fixed-cylinder radial operator estimate for the actual B0296 first heat-divergence
component. The normalized-cell factor cancels against the input normalization, leaving only the
explicit finite-cylinder weight comparison and the actual Gaussian `θ^(-1/2)` moment. -/
theorem eLpNorm_radialHeatDiv_fst_sq_le_radialInput {c θ m : ℝ} (hc : 0 < c)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hm : 0 ≤ m) {T : Plane → Plane × Plane}
    (hper : IsQPeriodic c T) (hT : Measurable T) :
    (eLpNorm (fun z => UnforcedLeray.B0579.bracket z ^ m * (heatDiv θ T z).1) 2
      (UnforcedLeray.Cyl.cellμ c)) ^ 2 ≤
      (ENNReal.ofReal ((1 + c ^ 2 / 4) ^ (m / 2)) *
        ENNReal.ofReal (2 ^ (m / 2) * θ ^ (-(1 / 2 : ℝ)) *
          ∫ w : Plane, gradKernelAxialMomentDensity 1 m w)) ^ 2 *
        (eLpNorm (fun z => UnforcedLeray.B0579.bracket z ^ m • T z) 2
          (UnforcedLeray.Cyl.cellμ c)) ^ 2 := by
  let f := fun z : Plane => axialWeight m z • T z
  have hfmeas : Measurable f := (continuous_axialWeight m).measurable.smul hT
  have hfper : IsQPeriodic c f := by
    intro z
    change axialWeight m (z.1 + c, z.2) • T (z.1 + c, z.2) = _
    rw [show axialWeight m (z.1 + c, z.2) = axialWeight m z by
      simp [axialWeight, axialBracket], hper z]
  have hCell := UnforcedLeray.HeatCylinder.eLpNorm_sq_cyl_eq_cellMeasure hc hfmeas hfper
  have hAxialLe : eLpNorm f 2 (UnforcedLeray.Cyl.cellμ c) ≤
      eLpNorm (fun z => UnforcedLeray.B0579.bracket z ^ m • T z) 2
        (UnforcedLeray.Cyl.cellμ c) := by
    have hPoint : ∀ᵐ z ∂UnforcedLeray.Cyl.cellμ c,
        ‖f z‖ₑ ≤ ‖UnforcedLeray.B0579.bracket z ^ m • T z‖ₑ := by
      filter_upwards [ae_restrict_mem (UnforcedLeray.Cyl.measurableSet_cell c)] with z hz
      have hweight := axialBracket_rpow_le_bracket hm z
      have hax : 0 ≤ axialWeight m z := by
        dsimp [axialWeight, axialBracket]
        positivity
      have hrad : 0 ≤ UnforcedLeray.B0579.bracket z ^ m :=
        (UnforcedLeray.B0579.bracket_rpow_pos m z).le
      rw [enorm_smul, Real.enorm_eq_ofReal_abs, abs_of_nonneg hax,
        enorm_smul, Real.enorm_eq_ofReal_abs, abs_of_nonneg hrad]
      exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hweight) (by positivity)
    exact eLpNorm_mono_enorm_ae hPoint
  have hInputSq : ENNReal.ofReal c *
      (eLpNorm f 2 (UnforcedLeray.B0284.cellMeasure c)) ^ 2 ≤
        (eLpNorm (fun z => UnforcedLeray.B0579.bracket z ^ m • T z) 2
          (UnforcedLeray.Cyl.cellμ c)) ^ 2 := by
    rw [← hCell]
    exact pow_le_pow_left₀ (by positivity) hAxialLe 2
  have hOut := eLpNorm_radialHeatDiv_fst_sq_le hc hθ hθ1 hm hper
    hT.aestronglyMeasurable
  let CcE : ℝ≥0∞ := ENNReal.ofReal ((1 + c ^ 2 / 4) ^ (m / 2))
  let KE : ℝ≥0∞ := ENNReal.ofReal (2 ^ (m / 2) * θ ^ (-(1 / 2 : ℝ)) *
    ∫ w : Plane, gradKernelAxialMomentDensity 1 m w)
  calc
    _ ≤ CcE ^ 2 * ENNReal.ofReal c *
        (KE * eLpNorm f 2 (UnforcedLeray.B0284.cellMeasure c)) ^ 2 := by
      simpa [CcE, KE] using hOut
    _ = (CcE * KE) ^ 2 *
        (ENNReal.ofReal c * (eLpNorm f 2
          (UnforcedLeray.B0284.cellMeasure c)) ^ 2) := by
      rw [mul_pow]
      ring
    _ ≤ (CcE * KE) ^ 2 *
        (eLpNorm (fun z => UnforcedLeray.B0579.bracket z ^ m • T z) 2
          (UnforcedLeray.Cyl.cellμ c)) ^ 2 :=
      mul_le_mul_of_nonneg_left hInputSq (by positivity)

/-- The same quantitative radial estimate holds for the sign-corrected response matching the
physical `−div F` source. -/
theorem eLpNorm_negativeHeatDiv_fst_sq_le_radialInput {c θ m : ℝ} (hc : 0 < c)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hm : 0 ≤ m) {T : Plane → Plane × Plane}
    (hper : IsQPeriodic c T) (hT : Measurable T) :
    (eLpNorm (fun z => UnforcedLeray.B0579.bracket z ^ m *
      (negativeHeatDiv θ T z).1) 2 (UnforcedLeray.Cyl.cellμ c)) ^ 2 ≤
      (ENNReal.ofReal ((1 + c ^ 2 / 4) ^ (m / 2)) *
        ENNReal.ofReal (2 ^ (m / 2) * θ ^ (-(1 / 2 : ℝ)) *
          ∫ w : Plane, gradKernelAxialMomentDensity 1 m w)) ^ 2 *
        (eLpNorm (fun z => UnforcedLeray.B0579.bracket z ^ m • T z) 2
          (UnforcedLeray.Cyl.cellμ c)) ^ 2 := by
  have h := eLpNorm_radialHeatDiv_fst_sq_le_radialInput hc hθ hθ1 hm hper hT
  have heq : (fun z => UnforcedLeray.B0579.bracket z ^ m *
      (negativeHeatDiv θ T z).1) =
      -(fun z => UnforcedLeray.B0579.bracket z ^ m *
        (UnforcedLeray.B0296.heatDiv θ T z).1) := by
    funext z
    simp [negativeHeatDiv, mul_neg]
  rw [heq, eLpNorm_neg]
  exact h

/-- Embed a two-component scalar flux as the first row of a planar tensor. The first component
of B0296's heat-divergence output is then exactly its scalar divergence heat response. -/
def scalarFluxTensor (Fq Fη : Plane → ℝ) : Plane → Plane × Plane :=
  fun z => ((Fq z, 0), (Fη z, 0))

/-- Scalar kernel integrand for the first row of the actual B0296 tensor heat-divergence. -/
def scalarFluxKernelIntegrand (θ : ℝ) (Fq Fη : Plane → ℝ) (z w : Plane) : ℝ :=
  (UnforcedLeray.B0296.gradHeatKernel2 θ w).1 * Fq (z - w) +
    (UnforcedLeray.B0296.gradHeatKernel2 θ w).2 * Fη (z - w)

theorem divKernel_scalarFluxTensor (θ : ℝ) (Fq Fη : Plane → ℝ) (z w : Plane) :
    UnforcedLeray.B0296.divKernel θ w (scalarFluxTensor Fq Fη (z - w)) =
      (scalarFluxKernelIntegrand θ Fq Fη z w, 0) := by
  simp [UnforcedLeray.B0296.divKernel, scalarFluxTensor, scalarFluxKernelIntegrand,
    smul_eq_mul]

/-- Cell integrability of a strongly measurable periodic field is preserved after any fixed
translation. The proof transports the finite integral of its ENNReal norm using the cylinder
fundamental-domain translation identity. -/
theorem integrable_translate_cell_of_periodic {c : ℝ} (hc : 0 < c)
    {f : Plane → ℝ} (hf : StronglyMeasurable f)
    (hper : UnforcedLeray.Cyl.IsPeriodic c f)
    (hint : Integrable f (volume.restrict (UnforcedLeray.Cyl.cell c))) (v : Plane) :
    Integrable (fun z => f (z + v)) (volume.restrict (UnforcedLeray.Cyl.cell c)) := by
  have hnormper : UnforcedLeray.Cyl.IsPeriodic c (fun z => ‖f z‖ₑ) := by
    intro z
    change ‖f (z.1 + c, z.2)‖ₑ = ‖f z‖ₑ
    rw [hper z]
  have hfinite : HasFiniteIntegral (fun z => f (z + v))
      (volume.restrict (UnforcedLeray.Cyl.cell c)) := by
    rw [hasFiniteIntegral_iff_enorm]
    rw [UnforcedLeray.Cyl.lintegral_cell_comp_add hc hnormper v]
    exact (hasFiniteIntegral_iff_enorm).1 hint.2
  refine ⟨?_, hfinite⟩
  exact (hf.comp_measurable (by fun_prop)).aestronglyMeasurable.mono_ac
    Measure.absolutelyContinuous_restrict

/-- Product integrability of the actual Gaussian-gradient/periodic-flux kernel follows from
cell `L¹` integrability of the two periodic flux components, integrability of the Gaussian
gradient coordinates, and joint measurability. The Fubini order integrates over one period cell
first, where periodic translation keeps both absolute flux integrals fixed. -/
theorem integrable_scalarFluxKernelIntegrand {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    {Fq Fη : Plane → ℝ}
    (hQper : UnforcedLeray.Cyl.IsPeriodic c Fq)
    (hEper : UnforcedLeray.Cyl.IsPeriodic c Fη)
    (hQint : ∀ w : Plane, Integrable (fun z => Fq (z - w))
      (volume.restrict (UnforcedLeray.Cyl.cell c)))
    (hEint : ∀ w : Plane, Integrable (fun z => Fη (z - w))
      (volume.restrict (UnforcedLeray.Cyl.cell c)))
    (hmeas : StronglyMeasurable
      (fun q : Plane × Plane => scalarFluxKernelIntegrand θ Fq Fη q.1 q.2)) :
    Integrable (fun q : Plane × Plane => scalarFluxKernelIntegrand θ Fq Fη q.1 q.2)
      ((volume.restrict (UnforcedLeray.Cyl.cell c)).prod volume) := by
  let μ : Measure Plane := volume.restrict (UnforcedLeray.Cyl.cell c)
  have hQabsper : UnforcedLeray.Cyl.IsPeriodic c (fun z => |Fq z|) := by
    intro z
    change |Fq (z.1 + c, z.2)| = |Fq z|
    rw [hQper z]
  have hEabsper : UnforcedLeray.Cyl.IsPeriodic c (fun z => |Fη z|) := by
    intro z
    change |Fη (z.1 + c, z.2)| = |Fη z|
    rw [hEper z]
  have hQshift : ∀ w : Plane,
      ∫ z in UnforcedLeray.Cyl.cell c, |Fq (z - w)| =
        ∫ z in UnforcedLeray.Cyl.cell c, |Fq z| := by
    intro w
    simpa only [sub_eq_add_neg] using
      UnforcedLeray.Cyl.integral_cell_comp_add hc hQabsper (-w)
  have hEshift : ∀ w : Plane,
      ∫ z in UnforcedLeray.Cyl.cell c, |Fη (z - w)| =
        ∫ z in UnforcedLeray.Cyl.cell c, |Fη z| := by
    intro w
    simpa only [sub_eq_add_neg] using
      UnforcedLeray.Cyl.integral_cell_comp_add hc hEabsper (-w)
  have hGq : Integrable (fun w : Plane => (UnforcedLeray.B0296.gradHeatKernel2 θ w).1)
      volume := by
    rw [show (fun w : Plane => (UnforcedLeray.B0296.gradHeatKernel2 θ w).1) =
      fun w => UnforcedLeray.B0296.dHeatKernel θ w.1 *
        UnforcedLeray.B0191.heatKernel 1 θ w.2 by rfl]
    exact (UnforcedLeray.B0296.integrable_dHeatKernel hθ).mul_prod
      (UnforcedLeray.B0296.integrable_heatKernel1 hθ)
  have hGη : Integrable (fun w : Plane => (UnforcedLeray.B0296.gradHeatKernel2 θ w).2)
      volume := by
    rw [show (fun w : Plane => (UnforcedLeray.B0296.gradHeatKernel2 θ w).2) =
      fun w => UnforcedLeray.B0191.heatKernel 1 θ w.1 *
        UnforcedLeray.B0296.dHeatKernel θ w.2 by rfl]
    exact (UnforcedLeray.B0296.integrable_heatKernel1 hθ).mul_prod
      (UnforcedLeray.B0296.integrable_dHeatKernel hθ)
  rw [integrable_prod_iff' hmeas.aestronglyMeasurable]
  constructor
  · filter_upwards [] with w
    exact ((hQint w).const_mul _).add ((hEint w).const_mul _)
  · have hOuterMeas : AEStronglyMeasurable
        (fun w : Plane => ∫ z in UnforcedLeray.Cyl.cell c,
          ‖scalarFluxKernelIntegrand θ Fq Fη z w‖) volume := by
      exact (hmeas.norm.integral_prod_left'
        (μ := volume.restrict (UnforcedLeray.Cyl.cell c))).aestronglyMeasurable
    let Q : ℝ := ∫ z in UnforcedLeray.Cyl.cell c, |Fq z|
    let E : ℝ := ∫ z in UnforcedLeray.Cyl.cell c, |Fη z|
    have hDom : Integrable (fun w : Plane =>
        |(UnforcedLeray.B0296.gradHeatKernel2 θ w).1| * Q +
          |(UnforcedLeray.B0296.gradHeatKernel2 θ w).2| * E) volume := by
      have hq := hGq.norm.const_mul Q
      have he := hGη.norm.const_mul E
      have hq' : Integrable (fun w : Plane =>
          |(UnforcedLeray.B0296.gradHeatKernel2 θ w).1| * Q) volume := by
        simpa [Q, Real.norm_eq_abs, mul_comm] using hq
      have he' : Integrable (fun w : Plane =>
          |(UnforcedLeray.B0296.gradHeatKernel2 θ w).2| * E) volume := by
        simpa [E, Real.norm_eq_abs, mul_comm] using he
      exact hq'.add he'
    refine hDom.mono' hOuterMeas ?_
    filter_upwards [] with w
    let a : ℝ := (UnforcedLeray.B0296.gradHeatKernel2 θ w).1
    let b : ℝ := (UnforcedLeray.B0296.gradHeatKernel2 θ w).2
    have hsec : Integrable (fun z : Plane =>
        scalarFluxKernelIntegrand θ Fq Fη z w) μ :=
      ((hQint w).const_mul a).add ((hEint w).const_mul b)
    have hQsecNorm : Integrable (fun z : Plane => |Fq (z - w)|) μ := by
      simpa [μ, Real.norm_eq_abs] using (hQint w).norm
    have hEsecNorm : Integrable (fun z : Plane => |Fη (z - w)|) μ := by
      simpa [μ, Real.norm_eq_abs] using (hEint w).norm
    have hbound : ∫ z in UnforcedLeray.Cyl.cell c,
        ‖scalarFluxKernelIntegrand θ Fq Fη z w‖ ≤ |a| * Q + |b| * E := by
      calc
        _ ≤ ∫ z in UnforcedLeray.Cyl.cell c,
            (|a| * |Fq (z - w)| + |b| * |Fη (z - w)|) := by
          apply integral_mono_ae hsec.norm
            ((hQsecNorm.const_mul |a|).add (hEsecNorm.const_mul |b|))
          filter_upwards [] with z
          rw [scalarFluxKernelIntegrand, Real.norm_eq_abs]
          calc
                |a * Fq (z - w) + b * Fη (z - w)| ≤
                |a * Fq (z - w)| + |b * Fη (z - w)| := abs_add_le _ _
            _ = |a| * |Fq (z - w)| + |b| * |Fη (z - w)| := by rw [abs_mul, abs_mul]
        _ = |a| * Q + |b| * E := by
          have hqa : Integrable (fun z : Plane => |a| * |Fq (z - w)|) μ := by
            simpa using hQsecNorm.const_mul |a|
          have hea : Integrable (fun z : Plane => |b| * |Fη (z - w)|) μ := by
            simpa using hEsecNorm.const_mul |b|
          calc
            _ = (∫ z in UnforcedLeray.Cyl.cell c, |a| * |Fq (z - w)|) +
                (∫ z in UnforcedLeray.Cyl.cell c, |b| * |Fη (z - w)|) :=
              integral_add hqa hea
            _ = |a| * (∫ z in UnforcedLeray.Cyl.cell c, |Fq (z - w)|) +
                |b| * (∫ z in UnforcedLeray.Cyl.cell c, |Fη (z - w)|) := by
              rw [integral_const_mul, integral_const_mul]
            _ = |a| * Q + |b| * E := by simp [Q, E, hQshift w, hEshift w]
    calc
      ‖∫ z in UnforcedLeray.Cyl.cell c,
          ‖scalarFluxKernelIntegrand θ Fq Fη z w‖‖ =
        ∫ z in UnforcedLeray.Cyl.cell c,
          ‖scalarFluxKernelIntegrand θ Fq Fη z w‖ :=
        Real.norm_of_nonneg (integral_nonneg fun z => norm_nonneg _)
      _ ≤ |a| * Q + |b| * E := hbound
      _ = |(UnforcedLeray.B0296.gradHeatKernel2 θ w).1| * Q +
          |(UnforcedLeray.B0296.gradHeatKernel2 θ w).2| * E := by
        simp [a, b]
/-- Fubini core of the actual zero-circulation heat response. Under product integrability of the
actual Gaussian-gradient/periodic-flux integrand, and cell integrability of every translated
flux slice, its first heat-divergence component has zero cell integral. The remaining supplier is
the product integrability bound, obtained for actual `X_m`, `m>1`, fluxes by weighted-to-`L¹`
Hölder and the `L¹` Gaussian gradient; it is deliberately stated here as a precise premise. -/
theorem integral_heatDiv_scalarFlux_eq_zero {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    {Fq Fη : Plane → ℝ}
    (hQper : UnforcedLeray.Cyl.IsPeriodic c Fq)
    (hEper : UnforcedLeray.Cyl.IsPeriodic c Fη)
    (hQint : ∀ w : Plane, Integrable (fun z => Fq (z - w))
      (volume.restrict (UnforcedLeray.Cyl.cell c)))
    (hEint : ∀ w : Plane, Integrable (fun z => Fη (z - w))
      (volume.restrict (UnforcedLeray.Cyl.cell c)))
    (hProd : Integrable (fun q : Plane × Plane =>
      scalarFluxKernelIntegrand θ Fq Fη q.1 q.2)
      ((volume.restrict (UnforcedLeray.Cyl.cell c)).prod volume)) :
    ∫ z in UnforcedLeray.Cyl.cell c,
      (UnforcedLeray.B0296.heatDiv θ (scalarFluxTensor Fq Fη) z).1 = 0 := by
  let μ : Measure Plane := volume.restrict (UnforcedLeray.Cyl.cell c)
  have hSections := hProd.prod_right_ae
  have hOutEq : (fun z : Plane =>
      (UnforcedLeray.B0296.heatDiv θ (scalarFluxTensor Fq Fη) z).1) =ᵐ[μ]
      fun z => ∫ w : Plane, scalarFluxKernelIntegrand θ Fq Fη z w := by
    filter_upwards [hSections] with z hz
    rw [UnforcedLeray.B0296.heatDiv_apply_of_pos hθ]
    have hvecEq : (fun w : Plane =>
        UnforcedLeray.B0296.divKernel θ w (scalarFluxTensor Fq Fη (z - w))) =
        fun w => (scalarFluxKernelIntegrand θ Fq Fη z w, 0) := by
      funext w
      exact divKernel_scalarFluxTensor θ Fq Fη z w
    have hvec : Integrable (fun w : Plane =>
        UnforcedLeray.B0296.divKernel θ w (scalarFluxTensor Fq Fη (z - w))) volume := by
      exact (hz.prodMk (integrable_zero (α := Plane) (ε' := ℝ) volume)).congr
        (Filter.Eventually.of_forall fun w => (congrFun hvecEq w).symm)
    rw [fst_integral hvec]
    exact integral_congr_ae (Filter.Eventually.of_forall fun w => by
      exact congrArg Prod.fst (divKernel_scalarFluxTensor θ Fq Fη z w))
  have hQshift : ∀ w : Plane,
      ∫ z in UnforcedLeray.Cyl.cell c, Fq (z - w) =
        ∫ z in UnforcedLeray.Cyl.cell c, Fq z := by
    intro w
    simpa only [sub_eq_add_neg] using
      UnforcedLeray.Cyl.integral_cell_comp_add hc hQper (-w)
  have hEshift : ∀ w : Plane,
      ∫ z in UnforcedLeray.Cyl.cell c, Fη (z - w) =
        ∫ z in UnforcedLeray.Cyl.cell c, Fη z := by
    intro w
    simpa only [sub_eq_add_neg] using
      UnforcedLeray.Cyl.integral_cell_comp_add hc hEper (-w)
  have hGq : Integrable (fun w : Plane => (UnforcedLeray.B0296.gradHeatKernel2 θ w).1)
      volume := by
    rw [show (fun w : Plane => (UnforcedLeray.B0296.gradHeatKernel2 θ w).1) =
      fun w => UnforcedLeray.B0296.dHeatKernel θ w.1 *
        UnforcedLeray.B0191.heatKernel 1 θ w.2 by rfl]
    exact (UnforcedLeray.B0296.integrable_dHeatKernel hθ).mul_prod
      (UnforcedLeray.B0296.integrable_heatKernel1 hθ)
  have hGη : Integrable (fun w : Plane => (UnforcedLeray.B0296.gradHeatKernel2 θ w).2)
      volume := by
    rw [show (fun w : Plane => (UnforcedLeray.B0296.gradHeatKernel2 θ w).2) =
      fun w => UnforcedLeray.B0191.heatKernel 1 θ w.1 *
        UnforcedLeray.B0296.dHeatKernel θ w.2 by rfl]
    exact (UnforcedLeray.B0296.integrable_heatKernel1 hθ).mul_prod
      (UnforcedLeray.B0296.integrable_dHeatKernel hθ)
  have hInner : ∀ w : Plane,
      ∫ z in UnforcedLeray.Cyl.cell c,
        scalarFluxKernelIntegrand θ Fq Fη z w =
          (UnforcedLeray.B0296.gradHeatKernel2 θ w).1 *
              (∫ z in UnforcedLeray.Cyl.cell c, Fq z) +
            (UnforcedLeray.B0296.gradHeatKernel2 θ w).2 *
              (∫ z in UnforcedLeray.Cyl.cell c, Fη z) := by
    intro w
    let a : ℝ := (UnforcedLeray.B0296.gradHeatKernel2 θ w).1
    let b : ℝ := (UnforcedLeray.B0296.gradHeatKernel2 θ w).2
    have hpoint : (fun z : Plane => scalarFluxKernelIntegrand θ Fq Fη z w) =
        fun z => a * Fq (z - w) + b * Fη (z - w) := by
      rfl
    have hQmul : ∫ z in UnforcedLeray.Cyl.cell c, a * Fq (z - w) =
        a * (∫ z in UnforcedLeray.Cyl.cell c, Fq z) := by
      rw [integral_const_mul, hQshift w]
    have hEmul : ∫ z in UnforcedLeray.Cyl.cell c, b * Fη (z - w) =
        b * (∫ z in UnforcedLeray.Cyl.cell c, Fη z) := by
      rw [integral_const_mul, hEshift w]
    calc
      _ = ∫ z in UnforcedLeray.Cyl.cell c,
          (a * Fq (z - w) + b * Fη (z - w)) := by
        exact integral_congr_ae (Filter.Eventually.of_forall fun z => congrFun hpoint z)
      _ = (∫ z in UnforcedLeray.Cyl.cell c,
          a * Fq (z - w)) +
          (∫ z in UnforcedLeray.Cyl.cell c,
          b * Fη (z - w)) :=
        integral_add ((hQint w).const_mul a) ((hEint w).const_mul b)
      _ = a * (∫ z in UnforcedLeray.Cyl.cell c, Fq z) +
          b * (∫ z in UnforcedLeray.Cyl.cell c, Fη z) := by rw [hQmul, hEmul]
  calc
    _ = ∫ z in UnforcedLeray.Cyl.cell c, ∫ w : Plane,
          scalarFluxKernelIntegrand θ Fq Fη z w := by
      exact integral_congr_ae hOutEq
    _ = ∫ w : Plane, ∫ z in UnforcedLeray.Cyl.cell c,
          scalarFluxKernelIntegrand θ Fq Fη z w := integral_integral_swap hProd
    _ = ∫ w : Plane,
          ((UnforcedLeray.B0296.gradHeatKernel2 θ w).1 *
              (∫ z in UnforcedLeray.Cyl.cell c, Fq z) +
            (UnforcedLeray.B0296.gradHeatKernel2 θ w).2 *
              (∫ z in UnforcedLeray.Cyl.cell c, Fη z)) := by
      exact integral_congr_ae (Filter.Eventually.of_forall hInner)
    _ = (∫ w : Plane, (UnforcedLeray.B0296.gradHeatKernel2 θ w).1) *
          (∫ z in UnforcedLeray.Cyl.cell c, Fq z) +
        (∫ w : Plane, (UnforcedLeray.B0296.gradHeatKernel2 θ w).2) *
          (∫ z in UnforcedLeray.Cyl.cell c, Fη z) := by
      have hOuter : ∫ w : Plane,
          ((UnforcedLeray.B0296.gradHeatKernel2 θ w).1 *
              (∫ z in UnforcedLeray.Cyl.cell c, Fq z) +
            (UnforcedLeray.B0296.gradHeatKernel2 θ w).2 *
              (∫ z in UnforcedLeray.Cyl.cell c, Fη z)) =
          (∫ w : Plane, (UnforcedLeray.B0296.gradHeatKernel2 θ w).1) *
              (∫ z in UnforcedLeray.Cyl.cell c, Fq z) +
            (∫ w : Plane, (UnforcedLeray.B0296.gradHeatKernel2 θ w).2) *
              (∫ z in UnforcedLeray.Cyl.cell c, Fη z) := by
        calc
          _ = (∫ w : Plane, (UnforcedLeray.B0296.gradHeatKernel2 θ w).1 *
                (∫ z in UnforcedLeray.Cyl.cell c, Fq z)) +
              (∫ w : Plane, (UnforcedLeray.B0296.gradHeatKernel2 θ w).2 *
                (∫ z in UnforcedLeray.Cyl.cell c, Fη z)) :=
            integral_add
              (hGq.mul_const (∫ z in UnforcedLeray.Cyl.cell c, Fq z))
              (hGη.mul_const (∫ z in UnforcedLeray.Cyl.cell c, Fη z))
          _ = _ := by rw [integral_mul_const, integral_mul_const]
      exact hOuter
    _ = 0 := by
      rw [integral_gradHeatKernel2_fst_eq_zero hθ,
        integral_gradHeatKernel2_snd_eq_zero hθ, zero_mul, zero_mul, zero_add]

/-- Zero circulation with the product-integrability premise discharged from periodic cell `L¹`
flux bounds, actual Gaussian-gradient integrability, and joint strong measurability. The remaining
input supplier is cell `L¹` integrability of each translated periodic flux slice. -/
theorem integral_heatDiv_scalarFlux_eq_zero_of_periodic_L1 {c θ : ℝ}
    (hc : 0 < c) (hθ : 0 < θ) {Fq Fη : Plane → ℝ}
    (hQper : UnforcedLeray.Cyl.IsPeriodic c Fq)
    (hEper : UnforcedLeray.Cyl.IsPeriodic c Fη)
    (hQint : ∀ w : Plane, Integrable (fun z => Fq (z - w))
      (volume.restrict (UnforcedLeray.Cyl.cell c)))
    (hEint : ∀ w : Plane, Integrable (fun z => Fη (z - w))
      (volume.restrict (UnforcedLeray.Cyl.cell c)))
    (hmeas : StronglyMeasurable
      (fun q : Plane × Plane => scalarFluxKernelIntegrand θ Fq Fη q.1 q.2)) :
    ∫ z in UnforcedLeray.Cyl.cell c,
      (UnforcedLeray.B0296.heatDiv θ (scalarFluxTensor Fq Fη) z).1 = 0 := by
  apply integral_heatDiv_scalarFlux_eq_zero hc hθ hQper hEper hQint hEint
  exact integrable_scalarFluxKernelIntegrand hc hθ hQper hEper hQint hEint hmeas

/-- Zero circulation from only cell `L¹` integrability of the two strongly measurable periodic
flux components. Periodic translation supplies every slice-integrability hypothesis, and the
Gaussian-gradient/Fubini product integrability is proved internally. -/
theorem integral_heatDiv_scalarFlux_eq_zero_of_cell_L1 {c θ : ℝ}
    (hc : 0 < c) (hθ : 0 < θ) {Fq Fη : Plane → ℝ}
    (hQper : UnforcedLeray.Cyl.IsPeriodic c Fq)
    (hEper : UnforcedLeray.Cyl.IsPeriodic c Fη)
    (hQsm : StronglyMeasurable Fq) (hEsm : StronglyMeasurable Fη)
    (hQbase : Integrable Fq (volume.restrict (UnforcedLeray.Cyl.cell c)))
    (hEbase : Integrable Fη (volume.restrict (UnforcedLeray.Cyl.cell c))) :
    ∫ z in UnforcedLeray.Cyl.cell c,
      (UnforcedLeray.B0296.heatDiv θ (scalarFluxTensor Fq Fη) z).1 = 0 := by
  have hFqcomp : StronglyMeasurable (fun q : Plane × Plane => Fq (q.1 - q.2)) :=
    hQsm.comp_measurable (by fun_prop)
  have hFecomp : StronglyMeasurable (fun q : Plane × Plane => Fη (q.1 - q.2)) :=
    hEsm.comp_measurable (by fun_prop)
  have hkq : Measurable (fun q : Plane × Plane =>
      (UnforcedLeray.B0296.gradHeatKernel2 θ q.2).1) :=
    (UnforcedLeray.B0296.measurable_gradHeatKernel2_fst θ).comp measurable_snd
  have hke : Measurable (fun q : Plane × Plane =>
      (UnforcedLeray.B0296.gradHeatKernel2 θ q.2).2) :=
    (UnforcedLeray.B0296.measurable_gradHeatKernel2_snd θ).comp measurable_snd
  have hmeas : StronglyMeasurable
      (fun q : Plane × Plane => scalarFluxKernelIntegrand θ Fq Fη q.1 q.2) := by
    have hqterm : StronglyMeasurable (fun q : Plane × Plane =>
        (UnforcedLeray.B0296.gradHeatKernel2 θ q.2).1 * Fq (q.1 - q.2)) :=
      hkq.stronglyMeasurable.mul hFqcomp
    have heterm : StronglyMeasurable (fun q : Plane × Plane =>
        (UnforcedLeray.B0296.gradHeatKernel2 θ q.2).2 * Fη (q.1 - q.2)) :=
      hke.stronglyMeasurable.mul hFecomp
    change StronglyMeasurable (fun q : Plane × Plane =>
      (UnforcedLeray.B0296.gradHeatKernel2 θ q.2).1 * Fq (q.1 - q.2) +
        (UnforcedLeray.B0296.gradHeatKernel2 θ q.2).2 * Fη (q.1 - q.2))
    rw [show (fun q : Plane × Plane =>
        (UnforcedLeray.B0296.gradHeatKernel2 θ q.2).1 * Fq (q.1 - q.2) +
          (UnforcedLeray.B0296.gradHeatKernel2 θ q.2).2 * Fη (q.1 - q.2)) =
        (fun q : Plane × Plane => (UnforcedLeray.B0296.gradHeatKernel2 θ q.2).1 *
          Fq (q.1 - q.2)) + (fun q => (UnforcedLeray.B0296.gradHeatKernel2 θ q.2).2 *
          Fη (q.1 - q.2)) by
      funext q
      rfl]
    exact hqterm.add heterm
  apply integral_heatDiv_scalarFlux_eq_zero_of_periodic_L1 hc hθ hQper hEper
  · intro w
    simpa only [sub_eq_add_neg] using
      integrable_translate_cell_of_periodic hc hQsm hQper hQbase (-w)
  · intro w
    simpa only [sub_eq_add_neg] using
      integrable_translate_cell_of_periodic hc hEsm hEper hEbase (-w)
  · exact hmeas

/-- The sign-corrected physical heat response still maps a radial weighted tensor input into
`X_m` on the centered cell. -/
theorem memLp_negativeHeatDiv_fst_X_of_radialInput {c θ m : ℝ} (hc : 0 < c)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hm : 0 ≤ m) {T : Plane → Plane × Plane}
    (hper : IsQPeriodic c T) (hT : Measurable T)
    (hRad : MemLp (fun z => UnforcedLeray.B0579.bracket z ^ m • T z) 2
      (UnforcedLeray.Cyl.cellμ c)) :
    MemLp (fun z => (negativeHeatDiv θ T z).1) 2
      (UnforcedLeray.B0579.cellMeasure c m) := by
  have h := memLp_heatDiv_fst_X_of_radialInput hc hθ hθ1 hm hper hT hRad
  change MemLp (fun z => -(UnforcedLeray.B0296.heatDiv θ T z).1) 2
    (UnforcedLeray.B0579.cellMeasure c m)
  exact h.neg

/-- The sign-corrected heat response preserves zero cell circulation under the same concrete
periodic-flux and Fubini hypotheses as `integral_heatDiv_scalarFlux_eq_zero`. This matches the
negative-divergence source from `B0610.curlSource` when the transport flux itself is passed in. -/
theorem integral_negativeHeatDiv_scalarFlux_eq_zero {c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ)
    {Fq Fη : Plane → ℝ}
    (hQper : UnforcedLeray.Cyl.IsPeriodic c Fq)
    (hEper : UnforcedLeray.Cyl.IsPeriodic c Fη)
    (hQint : ∀ w : Plane, Integrable (fun z => Fq (z - w))
      (volume.restrict (UnforcedLeray.Cyl.cell c)))
    (hEint : ∀ w : Plane, Integrable (fun z => Fη (z - w))
      (volume.restrict (UnforcedLeray.Cyl.cell c)))
    (hProd : Integrable (fun q : Plane × Plane =>
      scalarFluxKernelIntegrand θ Fq Fη q.1 q.2)
      ((volume.restrict (UnforcedLeray.Cyl.cell c)).prod volume)) :
    ∫ z in UnforcedLeray.Cyl.cell c,
      (negativeHeatDiv θ (scalarFluxTensor Fq Fη) z).1 = 0 := by
  have hcancel := integral_heatDiv_scalarFlux_eq_zero hc hθ hQper hEper hQint hEint hProd
  change ∫ z in UnforcedLeray.Cyl.cell c,
      -(UnforcedLeray.B0296.heatDiv θ (scalarFluxTensor Fq Fη) z).1 = 0
  rw [integral_neg, hcancel]
  simp

/-- Cell `L¹` periodic-flux version of zero circulation for the sign-corrected physical response
`−B0296.heatDiv`, matching B0610's `−div F` source. -/
theorem integral_negativeHeatDiv_scalarFlux_eq_zero_of_cell_L1 {c θ : ℝ}
    (hc : 0 < c) (hθ : 0 < θ) {Fq Fη : Plane → ℝ}
    (hQper : UnforcedLeray.Cyl.IsPeriodic c Fq)
    (hEper : UnforcedLeray.Cyl.IsPeriodic c Fη)
    (hQsm : StronglyMeasurable Fq) (hEsm : StronglyMeasurable Fη)
    (hQbase : Integrable Fq (volume.restrict (UnforcedLeray.Cyl.cell c)))
    (hEbase : Integrable Fη (volume.restrict (UnforcedLeray.Cyl.cell c))) :
    ∫ z in UnforcedLeray.Cyl.cell c,
      (negativeHeatDiv θ (scalarFluxTensor Fq Fη) z).1 = 0 := by
  have hpos := integral_heatDiv_scalarFlux_eq_zero_of_cell_L1 hc hθ hQper hEper
    hQsm hEsm hQbase hEbase
  change ∫ z in UnforcedLeray.Cyl.cell c,
      -(UnforcedLeray.B0296.heatDiv θ (scalarFluxTensor Fq Fη) z).1 = 0
  rw [integral_neg, hpos]
  simp

#print axioms eLpNorm_radialHeatDiv_fst_le_axialCyl
#print axioms eLpNorm_radialHeatDiv_fst_sq_le
#print axioms eLpNorm_radialHeatDiv_fst_sq_le_radialInput

#print axioms enorm_axial_weighted_divKernel_le
#print axioms eLpNorm_axialHeatDiv_le
#print axioms axialGradKernel_lintegral_le
#print axioms eLpNorm_axialHeatDiv_smoothing
#print axioms memLp_axialHeatDiv
#print axioms memLp_heatDiv_fst_X
#print axioms memLp_heatDiv_fst_X_of_radialInput
#print axioms integral_dHeatKernel_eq_zero
#print axioms integral_gradHeatKernel2_fst_eq_zero
#print axioms integral_gradHeatKernel2_snd_eq_zero
#print axioms integral_heatDiv_scalarFlux_eq_zero
#print axioms integral_negativeHeatDiv_scalarFlux_eq_zero
#print axioms integral_negativeHeatDiv_scalarFlux_eq_zero_of_cell_L1
#print axioms memLp_negativeHeatDiv_fst_X_of_radialInput
#print axioms eLpNorm_negativeHeatDiv_fst_sq_le_radialInput
#print axioms integrable_scalarFluxKernelIntegrand
#print axioms integral_heatDiv_scalarFlux_eq_zero_of_periodic_L1
#print axioms integrable_translate_cell_of_periodic
#print axioms integral_heatDiv_scalarFlux_eq_zero_of_cell_L1

end UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution
