import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.AxialHeatCommutatorBound
import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.KernelMoment

/-!
# Gaussian mass of the axial commutator kernel

This leaf records the exact weighted Gaussian moment needed by the commutator estimate. It keeps
the physical B0284 Gaussian and proves finiteness from the existing one-dimensional Gaussian
moment estimate.
-/

set_option autoImplicit false
set_option maxHeartbeats 500000

noncomputable section

open MeasureTheory
open Filter
open Set
open scoped ENNReal
open scoped Topology
open UnforcedLeray.GaussianVortex (Plane)

namespace UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

private theorem axialWeightDifferenceModulus_le_gaussianWeight {m : ℝ} (hm : 0 ≤ m)
    (η : ℝ) :
    axialWeightDifferenceModulus m (0, η) ≤ 2 ^ m * (1 + η ^ 2) ^ m := by
  let b : ℝ := 1 + 2 * |η| + |η| ^ 2
  have hbpos : 0 < b := by dsimp [b]; positivity
  have hb : b ≤ 2 * (1 + η ^ 2) := by
    dsimp [b]
    nlinarith [sq_nonneg (|η| - 1), abs_nonneg η, sq_abs η]
  have hpow : (b ^ (m / 2)) ^ 2 = b ^ m := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hbpos)]
    congr 1
    ring
  have hraise := Real.rpow_le_rpow (le_of_lt hbpos) hb hm
  rw [Real.mul_rpow (by norm_num) (by positivity)] at hraise
  have hmod : axialWeightDifferenceModulus m (0, η) = b ^ m - 1 := by
    dsimp [axialWeightDifferenceModulus, b]
    rw [hpow]
  rw [hmod]
  nlinarith [hraise, Real.rpow_nonneg (by positivity : 0 ≤ 1 + η ^ 2) m]

/-- The real Gaussian density defining the axial commutator kernel is integrable at each
positive age for every fixed real weight exponent `m≥0`. -/
theorem integrable_heatKernel2_mul_axialCommutatorModulus {θ m : ℝ}
    (hθ : 0 < θ) (hm : 0 ≤ m) :
    Integrable (fun w : Plane => B0284.heatKernel2 θ w *
      axialWeightDifferenceModulus m w) := by
  have hη := integrable_heatKernel1_mul_axialWeight (m := 2 * m) hθ (by linarith)
  have hq := B0296.integrable_heatKernel1 hθ
  have hdom : Integrable (fun η : ℝ =>
      2 ^ m * (B0191.heatKernel 1 θ η * (1 + η ^ 2) ^ m)) := by
    simpa [mul_assoc] using hη.const_mul (2 ^ m)
  have hmeas : AEStronglyMeasurable (fun η : ℝ =>
      B0191.heatKernel 1 θ η * axialWeightDifferenceModulus m (0, η)) volume := by
    have hcont : Continuous (fun η : ℝ =>
        B0191.heatKernel 1 θ η * axialWeightDifferenceModulus m (0, η)) := by
      have hb : Continuous (fun η : ℝ => 1 + 2 * |η| + |η| ^ 2) := by fun_prop
      have hp : Continuous (fun η : ℝ =>
          (1 + 2 * |η| + |η| ^ 2) ^ (m / 2)) :=
        (Real.continuous_rpow_const (q := m / 2) (by linarith)).comp hb
      have hmod : Continuous (fun η : ℝ =>
          axialWeightDifferenceModulus m (0, η)) := by
        change Continuous (fun η : ℝ =>
          ((1 + 2 * |η| + |η| ^ 2) ^ (m / 2)) ^ 2 - 1)
        exact (hp.pow 2).sub continuous_const
      exact (B0296.continuous_heatKernel1 θ).mul hmod
    exact hcont.aestronglyMeasurable
  have hη' : Integrable (fun η : ℝ =>
      B0191.heatKernel 1 θ η * axialWeightDifferenceModulus m (0, η)) := by
    refine hdom.mono' hmeas ?_
    filter_upwards [] with η
    have hk : 0 ≤ B0191.heatKernel 1 θ η :=
      B0191.heatKernel_pos one_pos hθ η |>.le
    have hmod := axialWeightDifferenceModulus_le_gaussianWeight hm η
    have hmod0 := axialWeightDifferenceModulus_nonneg hm (0, η)
    have hrad : 0 ≤ (1 + η ^ 2) ^ m := Real.rpow_nonneg (by positivity) _
    have hconst : 0 ≤ (2 : ℝ) ^ m := by positivity
    calc
      ‖B0191.heatKernel 1 θ η * axialWeightDifferenceModulus m (0, η)‖ =
          B0191.heatKernel 1 θ η * axialWeightDifferenceModulus m (0, η) := by
            rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hk hmod0)]
      _ ≤ 2 ^ m * (B0191.heatKernel 1 θ η * (1 + η ^ 2) ^ m) := by
            calc
              B0191.heatKernel 1 θ η * axialWeightDifferenceModulus m (0, η) ≤
                  B0191.heatKernel 1 θ η * (2 ^ m * (1 + η ^ 2) ^ m) :=
                    mul_le_mul_of_nonneg_left hmod hk
              _ = 2 ^ m * (B0191.heatKernel 1 θ η * (1 + η ^ 2) ^ m) := by ring
  rw [show (fun w : Plane => B0284.heatKernel2 θ w *
      axialWeightDifferenceModulus m w) =
      fun w : ℝ × ℝ => B0191.heatKernel 1 θ w.1 *
        (B0191.heatKernel 1 θ w.2 * axialWeightDifferenceModulus m (0, w.2)) by
          funext w
          simp [B0284.heatKernel2, axialWeightDifferenceModulus, sq_abs]
          ring]
  exact hq.mul_prod hη'

/-- The ENNReal mass in the commutator estimate is finite at every positive age. -/
theorem axialHeatCommutatorKernel_lintegral_lt_top {θ m : ℝ}
    (hθ : 0 < θ) (hm : 0 ≤ m) :
    (∫⁻ w : Plane, axialHeatCommutatorKernel θ m w) < ⊤ := by
  rw [show (fun w : Plane => axialHeatCommutatorKernel θ m w) =
      fun w => ENNReal.ofReal (B0284.heatKernel2 θ w *
        axialWeightDifferenceModulus m w) by rfl]
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrable_heatKernel2_mul_axialCommutatorModulus hθ hm)
    (Eventually.of_forall fun w => mul_nonneg
      (B0284.heatKernel2_nonneg hθ w)
      (axialWeightDifferenceModulus_nonneg hm w))]
  exact ENNReal.ofReal_lt_top

/-- Parabolic scaling of the actual planar B0284 Gaussian. -/
theorem heatKernel2_scale_sqr {r : ℝ} (hr : 0 < r) (w : Plane) :
    B0284.heatKernel2 (r ^ 2) (r • w) =
      (r ^ 2)⁻¹ * B0284.heatKernel2 1 w := by
  change B0191.heatKernel 1 (r ^ 2) (r * w.1) *
      B0191.heatKernel 1 (r ^ 2) (r * w.2) =
    (r ^ 2)⁻¹ * (B0191.heatKernel 1 1 w.1 * B0191.heatKernel 1 1 w.2)
  rw [heatKernel_scale_sqr hr, heatKernel_scale_sqr hr]
  field_simp

/-- Exact dilation identity for the commutator Gaussian mass: after `w=√θ v`, the unit-age
Gaussian remains and only the axial ratio modulus is evaluated at the shrinking shift. -/
theorem integral_heatKernel2_mul_axialCommutatorModulus_eq_dilated {θ m : ℝ}
    (hθ : 0 < θ) (hm : 0 ≤ m) :
    ∫ w : Plane, B0284.heatKernel2 θ w * axialWeightDifferenceModulus m w =
      ∫ w : Plane, B0284.heatKernel2 1 w *
        axialWeightDifferenceModulus m (Real.sqrt θ • w) := by
  let r : ℝ := Real.sqrt θ
  have hr : 0 < r := by dsimp [r]; exact Real.sqrt_pos.2 hθ
  have hr2 : r ^ 2 = θ := by dsimp [r]; exact Real.sq_sqrt hθ.le
  let F : Plane → ℝ := fun w =>
    B0284.heatKernel2 θ w * axialWeightDifferenceModulus m w
  have hchange := MeasureTheory.Measure.integral_comp_smul (volume : Measure Plane) F r
  have hdim : Module.finrank ℝ Plane = 2 := by simp [Plane, Module.finrank_prod]
  rw [hdim] at hchange
  have hchange' : ∫ w : Plane, F (r • w) = (r ^ 2)⁻¹ * ∫ w : Plane, F w := by
    simpa [abs_of_pos hr, smul_eq_mul, Real.rpow_neg hr.le, Real.rpow_natCast] using hchange
  have hscaled : ∀ w : Plane, F (r • w) = (r ^ 2)⁻¹ *
      (B0284.heatKernel2 1 w * axialWeightDifferenceModulus m (r • w)) := by
    intro w
    dsimp [F]
    rw [← hr2, heatKernel2_scale_sqr hr]
    ring
  have hscaledInt : ∫ w : Plane, F (r • w) = (r ^ 2)⁻¹ *
      ∫ w : Plane, B0284.heatKernel2 1 w * axialWeightDifferenceModulus m (r • w) := by
    simp_rw [hscaled]
    rw [integral_const_mul]
  have hcancel := hscaledInt.symm.trans hchange'
  have hcoef : (r ^ 2)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero 2 hr.ne')
  have heq : ∫ w : Plane, B0284.heatKernel2 1 w *
      axialWeightDifferenceModulus m (r • w) = ∫ w : Plane, F w :=
    mul_left_cancel₀ hcoef hcancel
  simpa [F, hr2, r] using heq.symm

/-- The axial ratio modulus decreases under a dilation by `0≤r≤1`. -/
theorem axialWeightDifferenceModulus_dilate_le {m r : ℝ} (hm : 0 ≤ m)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (w : Plane) :
    axialWeightDifferenceModulus m (r • w) ≤ axialWeightDifferenceModulus m w := by
  let h : ℝ := |w.2|
  have hh : 0 ≤ h := abs_nonneg _
  have hshift : |(r • w).2| = r * h := by
    simp [h, abs_mul, abs_of_nonneg hr0]
  have hshiftle : r * h ≤ h := by nlinarith [mul_le_mul_of_nonneg_right hr1 hh]
  have hshiftSq : (r * h) ^ 2 ≤ h ^ 2 := by
    nlinarith [sq_nonneg (h - r * h)]
  have hbase : 1 + 2 * |(r • w).2| + |(r • w).2| ^ 2 ≤
      1 + 2 * h + h ^ 2 := by rw [hshift]; nlinarith [hshiftle, hshiftSq]
  have hC : (1 + 2 * |(r • w).2| + |(r • w).2| ^ 2) ^ (m / 2) ≤
      (1 + 2 * h + h ^ 2) ^ (m / 2) :=
    Real.rpow_le_rpow (by positivity) hbase (by linarith)
  have hC0 : 0 ≤ (1 + 2 * |(r • w).2| + |(r • w).2| ^ 2) ^ (m / 2) :=
    Real.rpow_nonneg (by positivity) _
  have hC1 : 0 ≤ (1 + 2 * h + h ^ 2) ^ (m / 2) := Real.rpow_nonneg (by positivity) _
  unfold axialWeightDifferenceModulus
  rw [hshift]
  have hsquare := mul_le_mul hC hC hC0 hC1
  rw [hshift] at hsquare
  dsimp [h] at hsquare ⊢
  nlinarith [hsquare]

/-- Continuity of the axial ratio modulus as a function of the planar shift. -/
theorem continuous_axialWeightDifferenceModulus {m : ℝ} (hm : 0 ≤ m) :
    Continuous (axialWeightDifferenceModulus m) := by
  have hb : Continuous (fun w : Plane => 1 + 2 * |w.2| + |w.2| ^ 2) := by fun_prop
  have hp : Continuous (fun w : Plane =>
      (1 + 2 * |w.2| + |w.2| ^ 2) ^ (m / 2)) :=
    (Real.continuous_rpow_const (q := m / 2) (by linarith)).comp hb
  change Continuous (fun w : Plane =>
    ((1 + 2 * |w.2| + |w.2| ^ 2) ^ (m / 2)) ^ 2 - 1)
  exact (hp.pow 2).sub continuous_const

/-- The actual rescaled Gaussian commutator mass tends to zero at zero. The proof uses the exact
two-dimensional parabolic dilation, the shrinking axial modulus, and the integrable unit-age
Gaussian polynomial majorant. -/
theorem tendsto_integral_unitHeat_axialCommutatorModulus_zero {m : ℝ} (hm : 0 ≤ m) :
    Tendsto (fun θ : ℝ => ∫ w : Plane, B0284.heatKernel2 1 w *
      axialWeightDifferenceModulus m (Real.sqrt θ • w))
      (nhdsWithin (0 : ℝ) (Ioi 0)) (𝓝 (0 : ℝ)) := by
  let F : ℝ → Plane → ℝ := fun θ w =>
    B0284.heatKernel2 1 w * axialWeightDifferenceModulus m (Real.sqrt θ • w)
  let G : Plane → ℝ := fun w =>
    B0284.heatKernel2 1 w * axialWeightDifferenceModulus m w
  have hG : Integrable G := by
    simpa [G] using integrable_heatKernel2_mul_axialCommutatorModulus one_pos hm
  have hmeas : ∀ θ : ℝ, AEStronglyMeasurable (F θ) volume := by
    intro θ
    have hs : Continuous (fun w : Plane => Real.sqrt θ • w) :=
      continuous_const_smul (Real.sqrt θ)
    have hmod : Continuous (fun w : Plane =>
        axialWeightDifferenceModulus m (Real.sqrt θ • w)) :=
      (continuous_axialWeightDifferenceModulus hm).comp hs
    have hK : Continuous (fun w : Plane => B0284.heatKernel2 1 w) := by
      change Continuous (fun w : ℝ × ℝ =>
        B0191.heatKernel 1 1 w.1 * B0191.heatKernel 1 1 w.2)
      exact (B0296.continuous_heatKernel1 1).comp continuous_fst |>.mul
        ((B0296.continuous_heatKernel1 1).comp continuous_snd)
    exact (hK.mul hmod).aestronglyMeasurable
  have hbound : ∀ᶠ θ : ℝ in nhdsWithin (0 : ℝ) (Ioi 0), ∀ᵐ w ∂volume, ‖F θ w‖ ≤ G w := by
    have hlt0 : ∀ᶠ θ : ℝ in 𝓝 (0 : ℝ), θ < 1 := by
      exact Iio_mem_nhds (by norm_num : (0 : ℝ) < 1)
    have hlt : ∀ᶠ θ : ℝ in nhdsWithin (0 : ℝ) (Ioi 0), θ < 1 :=
      hlt0.filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, hlt] with θ hθ hθ1
    filter_upwards [] with w
    let r := Real.sqrt θ
    have hr0 : 0 ≤ r := by dsimp [r]; positivity
    have hr1 : r ≤ 1 := by
      dsimp [r]
      exact Real.sqrt_le_one.mpr (by linarith)
    have hmod := axialWeightDifferenceModulus_dilate_le hm hr0 hr1 w
    have hK : 0 ≤ B0284.heatKernel2 1 w := B0284.heatKernel2_nonneg one_pos w
    have hD : 0 ≤ axialWeightDifferenceModulus m (r • w) :=
      axialWeightDifferenceModulus_nonneg hm (r • w)
    have hG0 : 0 ≤ G w := mul_nonneg hK
      (axialWeightDifferenceModulus_nonneg hm w)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hK hD)]
    exact mul_le_mul_of_nonneg_left (by simpa [r, F, G] using hmod) hK
  have hpoint : ∀ᵐ w ∂volume, Tendsto (fun θ => F θ w)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (𝓝 (0 : ℝ)) := by
    filter_upwards [] with w
    have hsqrt : Tendsto (fun θ : ℝ => Real.sqrt θ)
        (nhdsWithin (0 : ℝ) (Ioi 0)) (𝓝 (0 : ℝ)) := by
      rw [Metric.tendsto_nhds]
      intro ε hε
      have hlt0 : ∀ᶠ θ : ℝ in 𝓝 (0 : ℝ), θ < ε ^ 2 := by
        exact Iio_mem_nhds (sq_pos_of_pos hε)
      have hlt : ∀ᶠ θ : ℝ in nhdsWithin (0 : ℝ) (Ioi 0), θ < ε ^ 2 :=
        hlt0.filter_mono nhdsWithin_le_nhds
      filter_upwards [self_mem_nhdsWithin, hlt] with θ hθ hθ2
      have hs : Real.sqrt θ < ε := by
        calc
          Real.sqrt θ < Real.sqrt (ε ^ 2) := Real.sqrt_lt_sqrt hθ.le hθ2
          _ = ε := by rw [Real.sqrt_sq_eq_abs, abs_of_pos hε]
      simpa [Real.dist_eq, abs_of_nonneg (Real.sqrt_nonneg _)] using hs
    have hshift : Tendsto (fun θ : ℝ => Real.sqrt θ • w)
        (nhdsWithin (0 : ℝ) (Ioi 0)) (𝓝 (0 : Plane)) := by
      simpa using hsqrt.smul_const w
    have hmod := ((continuous_axialWeightDifferenceModulus hm).tendsto (0 : Plane)).comp hshift
    have hzero : axialWeightDifferenceModulus m (0 : Plane) = 0 := by
      simp [axialWeightDifferenceModulus]
    have hterm : Tendsto (fun θ : ℝ =>
        axialWeightDifferenceModulus m (Real.sqrt θ • w))
        (nhdsWithin (0 : ℝ) (Ioi 0)) (𝓝 (0 : ℝ)) := by
      simpa [hzero, Function.comp_def] using hmod
    have hmul := (tendsto_const_nhds : Tendsto (fun _ : ℝ => B0284.heatKernel2 1 w)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (𝓝 (B0284.heatKernel2 1 w))).mul hterm
    simpa [F] using hmul
  have hDCT := tendsto_integral_filter_of_dominated_convergence
    (μ := volume) (l := nhdsWithin (0 : ℝ) (Ioi 0))
    (F := F) (f := fun _ => (0 : ℝ)) G
    (by filter_upwards [] with θ; exact hmeas θ) hbound hG hpoint
  simpa [F] using hDCT

/-- The ENNReal mass in the actual commutator estimate tends to zero as the positive heat age
shrinks to zero. -/
theorem tendsto_axialHeatCommutatorKernel_lintegral_zero {m : ℝ} (hm : 0 ≤ m) :
    Tendsto (fun θ : ℝ => ∫⁻ w : Plane, axialHeatCommutatorKernel θ m w)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (𝓝 (0 : ℝ≥0∞)) := by
  have hreal := (tendsto_integral_unitHeat_axialCommutatorModulus_zero hm)
  have hreal' : Tendsto (fun θ : ℝ =>
      ∫ w : Plane, B0284.heatKernel2 θ w * axialWeightDifferenceModulus m w)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (𝓝 (0 : ℝ)) := by
    have hEq : ∀ᶠ θ : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
        (∫ w : Plane, B0284.heatKernel2 θ w * axialWeightDifferenceModulus m w) =
          ∫ w : Plane, B0284.heatKernel2 1 w *
            axialWeightDifferenceModulus m (Real.sqrt θ • w) := by
      filter_upwards [self_mem_nhdsWithin] with θ hθ
      exact integral_heatKernel2_mul_axialCommutatorModulus_eq_dilated hθ hm
    have hEq' : (fun θ : ℝ =>
        ∫ w : Plane, B0284.heatKernel2 1 w *
          axialWeightDifferenceModulus m (Real.sqrt θ • w)) =ᶠ[
            nhdsWithin (0 : ℝ) (Ioi 0)] (fun θ =>
              ∫ w : Plane, B0284.heatKernel2 θ w *
                axialWeightDifferenceModulus m w) := by
      filter_upwards [hEq] with θ hθ
      exact hθ.symm
    exact hreal.congr' hEq'
  have hENN : Tendsto (fun θ : ℝ => ENNReal.ofReal
      (∫ w : Plane, B0284.heatKernel2 θ w * axialWeightDifferenceModulus m w))
      (nhdsWithin (0 : ℝ) (Ioi 0)) (𝓝 (0 : ℝ≥0∞)) := by
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp hreal'
  have hmass : ∀ᶠ θ : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
      (∫⁻ w : Plane, axialHeatCommutatorKernel θ m w) =
        ENNReal.ofReal (∫ w : Plane,
          B0284.heatKernel2 θ w * axialWeightDifferenceModulus m w) := by
    filter_upwards [self_mem_nhdsWithin] with θ hθ
    rw [show (fun w : Plane => axialHeatCommutatorKernel θ m w) =
      fun w => ENNReal.ofReal (B0284.heatKernel2 θ w *
        axialWeightDifferenceModulus m w) by rfl]
    rw [← ofReal_integral_eq_lintegral_ofReal
      (integrable_heatKernel2_mul_axialCommutatorModulus hθ hm)
      (Eventually.of_forall fun w => mul_nonneg
        (B0284.heatKernel2_nonneg hθ w)
        (axialWeightDifferenceModulus_nonneg hm w))]
  have hmass' : (fun θ : ℝ => ENNReal.ofReal (∫ w : Plane,
        B0284.heatKernel2 θ w * axialWeightDifferenceModulus m w)) =ᶠ[
          nhdsWithin (0 : ℝ) (Ioi 0)] (fun θ =>
            ∫⁻ w : Plane, axialHeatCommutatorKernel θ m w) := by
    filter_upwards [hmass] with θ hθ
    exact hθ.symm
  exact hENN.congr' hmass'

#print axioms heatKernel2_scale_sqr
#print axioms integral_heatKernel2_mul_axialCommutatorModulus_eq_dilated
#print axioms axialWeightDifferenceModulus_dilate_le
#print axioms continuous_axialWeightDifferenceModulus
#print axioms tendsto_integral_unitHeat_axialCommutatorModulus_zero
#print axioms tendsto_axialHeatCommutatorKernel_lintegral_zero

#print axioms axialWeightDifferenceModulus_le_gaussianWeight
#print axioms integrable_heatKernel2_mul_axialCommutatorModulus
#print axioms axialHeatCommutatorKernel_lintegral_lt_top

end UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution
