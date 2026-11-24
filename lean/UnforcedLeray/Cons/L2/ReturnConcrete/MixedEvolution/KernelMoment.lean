import UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.WeightedKernel
import UnforcedLeray.Units.B0296.Kernel
import Mathlib.Probability.Moments.IntegrableExpMul

/-!
# Finite axial Gaussian moments for the weighted heat-divergence kernel

These lemmas prove the polynomially weighted one-dimensional Gaussian and derivative kernels are
integrable for every real `m ≥ 0`. They are the finiteness input for the two-dimensional weighted
gradient-kernel moment. The later scaling lemma will turn that moment into the explicit
`θ^(-1/2)` heat-divergence bound on `0 < θ ≤ 1`.
-/

set_option autoImplicit false
set_option maxHeartbeats 500000

noncomputable section

namespace UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

open MeasureTheory Filter
open UnforcedLeray.B0296
open UnforcedLeray.GaussianVortex (Plane)

/-- Every nonnegative power moment of a one-dimensional Gaussian is integrable. -/
theorem integrable_sq_rpow_mul_gaussian {b p : ℝ} (hb : 0 < b) (hp : 0 ≤ p) :
    Integrable (fun x : ℝ => (x ^ 2) ^ p * Real.exp (-b * x ^ 2)) := by
  have ht : b / 2 ≠ 0 := ne_of_gt (by positivity)
  have hpos : Integrable (fun x : ℝ => Real.exp ((-b + b / 2) * x ^ 2)) := by
    convert integrable_exp_neg_mul_sq (by positivity : 0 < b / 2) using 1 <;> congr 1 <;> ring
  have hneg : Integrable (fun x : ℝ => Real.exp ((-b - b / 2) * x ^ 2)) := by
    convert integrable_exp_neg_mul_sq (by positivity : 0 < b + b / 2) using 1 <;> congr 1 <;> ring
  exact ProbabilityTheory.integrable_rpow_mul_exp_of_integrable_exp_mul
    (μ := (volume : Measure ℝ)) (X := fun x : ℝ => x ^ 2) (v := -b) (t := b / 2)
    ht hpos hneg hp

/-- The axial polynomial weight times a Gaussian remains integrable for arbitrary real `m≥0`. -/
theorem integrable_axialGaussianWeight {b m : ℝ} (hb : 0 < b) (hm : 0 ≤ m) :
    Integrable (fun x : ℝ => (1 + x ^ 2) ^ (m / 2) * Real.exp (-b * x ^ 2)) := by
  let α := m / 2
  have hα : 0 ≤ α := by dsimp [α]; linarith
  have hzero : Integrable (fun x : ℝ => Real.exp (-b * x ^ 2)) := integrable_exp_neg_mul_sq hb
  have hmoment := integrable_sq_rpow_mul_gaussian hb hα
  have hsum : Integrable (fun x : ℝ =>
      Real.exp (-b * x ^ 2) + (x ^ 2) ^ α * Real.exp (-b * x ^ 2)) := hzero.add hmoment
  have hmajor : Integrable (fun x : ℝ => 2 ^ α *
      (Real.exp (-b * x ^ 2) + (x ^ 2) ^ α * Real.exp (-b * x ^ 2))) := by
    simpa [mul_comm] using hsum.const_mul (2 ^ α)
  refine hmajor.mono' ?_ ?_
  · fun_prop
  · filter_upwards [] with x
    have ht : 0 ≤ x ^ 2 := sq_nonneg x
    have hbase : 1 + x ^ 2 ≤ 2 * max 1 (x ^ 2) := by
      have h1 := le_max_left (1 : ℝ) (x ^ 2)
      have h2 := le_max_right (1 : ℝ) (x ^ 2)
      nlinarith
    have hweight : (1 + x ^ 2) ^ α ≤ 2 ^ α * (1 + (x ^ 2) ^ α) := by
      calc
        (1 + x ^ 2) ^ α ≤ (2 * max 1 (x ^ 2)) ^ α :=
          Real.rpow_le_rpow (by positivity) hbase hα
        _ = 2 ^ α * (max 1 (x ^ 2)) ^ α := by
          rw [Real.mul_rpow (by norm_num) (by positivity)]
        _ ≤ 2 ^ α * (1 + (x ^ 2) ^ α) := by
          have hmax : (max 1 (x ^ 2)) ^ α = max 1 ((x ^ 2) ^ α) := by
            have h := Real.rpow_max (x := (1 : ℝ)) (y := x ^ 2) (p := α)
              (by norm_num) ht hα
            simpa using h
          rw [hmax]
          have hy : 0 ≤ (x ^ 2) ^ α := Real.rpow_nonneg ht α
          have hle : max 1 ((x ^ 2) ^ α) ≤ 1 + (x ^ 2) ^ α :=
            max_le (by linarith [hy]) (by linarith)
          exact mul_le_mul_of_nonneg_left hle (by positivity)
    have hn : 0 ≤ (1 + x ^ 2) ^ α * Real.exp (-b * x ^ 2) :=
      mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.exp_pos _).le
    have hmj : 0 ≤ 2 ^ α *
        (Real.exp (-b * x ^ 2) + (x ^ 2) ^ α * Real.exp (-b * x ^ 2)) := by
      positivity
    calc
      ‖(1 + x ^ 2) ^ α * Real.exp (-b * x ^ 2)‖ =
          (1 + x ^ 2) ^ α * Real.exp (-b * x ^ 2) := by
            rw [Real.norm_eq_abs, abs_of_nonneg hn]
      _ ≤ 2 ^ α * (1 + (x ^ 2) ^ α) * Real.exp (-b * x ^ 2) :=
        mul_le_mul_of_nonneg_right hweight (Real.exp_pos _).le
      _ = 2 ^ α *
          (Real.exp (-b * x ^ 2) + (x ^ 2) ^ α * Real.exp (-b * x ^ 2)) := by ring

/-- One-dimensional B0191 Gaussian scaling in the exact normalization used by B0296. -/
theorem heatKernel_scale_sqr {r : ℝ} (hr : 0 < r) (x : ℝ) :
    UnforcedLeray.B0191.heatKernel 1 (r ^ 2) (r * x) =
      r⁻¹ * UnforcedLeray.B0191.heatKernel 1 1 x := by
  have hroot : Real.sqrt (4 * Real.pi * 1 * r ^ 2) =
      r * Real.sqrt (4 * Real.pi * 1 * 1) := by
    rw [show 4 * Real.pi * 1 * r ^ 2 = (4 * Real.pi * 1 * 1) * r ^ 2 by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq_eq_abs, abs_of_pos hr]
    ring
  have hexp : -(r * x) ^ 2 / (4 * 1 * r ^ 2) = -x ^ 2 / (4 * 1 * 1) := by
    field_simp
  unfold UnforcedLeray.B0191.heatKernel
  rw [hroot, hexp]
  field_simp

/-- The derivative of the B0191 Gaussian has the corresponding `r⁻²` scaling. -/
theorem dHeatKernel_scale_sqr {r : ℝ} (hr : 0 < r) (x : ℝ) :
    UnforcedLeray.B0296.dHeatKernel (r ^ 2) (r * x) =
      (r ^ 2)⁻¹ * UnforcedLeray.B0296.dHeatKernel 1 x := by
  unfold UnforcedLeray.B0296.dHeatKernel
  rw [heatKernel_scale_sqr hr]
  have hrne : r ≠ 0 := ne_of_gt hr
  field_simp

/-- The actual B0296 planar heat-gradient scales like a derivative of a two-dimensional
Gaussian. -/
theorem gradHeatKernel2_scale_sqr {r : ℝ} (hr : 0 < r) (w : Plane) :
    UnforcedLeray.B0296.gradHeatKernel2 (r ^ 2) (r • w) =
      (r ^ 3)⁻¹ • UnforcedLeray.B0296.gradHeatKernel2 1 w := by
  apply Prod.ext
  · change UnforcedLeray.B0296.dHeatKernel (r ^ 2) (r * w.1) *
      UnforcedLeray.B0191.heatKernel 1 (r ^ 2) (r * w.2) =
      (r ^ 3)⁻¹ * (UnforcedLeray.B0296.dHeatKernel 1 w.1 *
        UnforcedLeray.B0191.heatKernel 1 1 w.2)
    rw [dHeatKernel_scale_sqr hr, heatKernel_scale_sqr hr]
    field_simp
  · change UnforcedLeray.B0191.heatKernel 1 (r ^ 2) (r * w.1) *
      UnforcedLeray.B0296.dHeatKernel (r ^ 2) (r * w.2) =
      (r ^ 3)⁻¹ * (UnforcedLeray.B0191.heatKernel 1 1 w.1 *
        UnforcedLeray.B0296.dHeatKernel 1 w.2)
    rw [heatKernel_scale_sqr hr, dHeatKernel_scale_sqr hr]
    field_simp

/-- Real density of the axial-weighted absolute gradient moment. -/
def gradKernelAxialMomentDensity (θ m : ℝ) (w : Plane) : ℝ :=
  (‖(UnforcedLeray.B0296.gradHeatKernel2 θ w).1‖ +
    ‖(UnforcedLeray.B0296.gradHeatKernel2 θ w).2‖) * (1 + w.2 ^ 2) ^ (m / 2)

/-- Under the parabolic dilation, the actual gradient costs `r⁻³`; the axial weight only
improves when `r²≤1`. -/
theorem gradKernelAxialMomentDensity_scale_le {r m : ℝ} (hr : 0 < r)
    (hr2 : r ^ 2 ≤ 1) (hm : 0 ≤ m) (w : Plane) :
    gradKernelAxialMomentDensity (r ^ 2) m (r • w) ≤
      (r ^ 3)⁻¹ * gradKernelAxialMomentDensity 1 m w := by
  have hc : 0 ≤ (r ^ 3)⁻¹ := by positivity
  have hgrad :
      (‖(UnforcedLeray.B0296.gradHeatKernel2 (r ^ 2) (r • w)).1‖ +
        ‖(UnforcedLeray.B0296.gradHeatKernel2 (r ^ 2) (r • w)).2‖) =
      (r ^ 3)⁻¹ *
        (‖(UnforcedLeray.B0296.gradHeatKernel2 1 w).1‖ +
          ‖(UnforcedLeray.B0296.gradHeatKernel2 1 w).2‖) := by
    rw [gradHeatKernel2_scale_sqr hr]
    simp [Real.norm_of_nonneg hc]
    ring
  have hbase : 1 + (r * w.2) ^ 2 ≤ 1 + w.2 ^ 2 := by
    rw [mul_pow]
    nlinarith [sq_nonneg w.2]
  have hweight : (1 + (r * w.2) ^ 2) ^ (m / 2) ≤
      (1 + w.2 ^ 2) ^ (m / 2) :=
    Real.rpow_le_rpow (by positivity) hbase (by linarith)
  unfold gradKernelAxialMomentDensity
  rw [hgrad]
  simp only [Prod.smul_snd, smul_eq_mul]
  calc
    (r ^ 3)⁻¹ *
        (‖(UnforcedLeray.B0296.gradHeatKernel2 1 w).1‖ +
          ‖(UnforcedLeray.B0296.gradHeatKernel2 1 w).2‖) *
        (1 + (r * w.2) ^ 2) ^ (m / 2) =
      ((r ^ 3)⁻¹ *
        (‖(UnforcedLeray.B0296.gradHeatKernel2 1 w).1‖ +
          ‖(UnforcedLeray.B0296.gradHeatKernel2 1 w).2‖)) *
        (1 + (r * w.2) ^ 2) ^ (m / 2) := by ring
    _ ≤ ((r ^ 3)⁻¹ *
        (‖(UnforcedLeray.B0296.gradHeatKernel2 1 w).1‖ +
          ‖(UnforcedLeray.B0296.gradHeatKernel2 1 w).2‖)) *
        (1 + w.2 ^ 2) ^ (m / 2) :=
      mul_le_mul_of_nonneg_left hweight (by positivity)
    _ = (r ^ 3)⁻¹ *
        ((‖(UnforcedLeray.B0296.gradHeatKernel2 1 w).1‖ +
          ‖(UnforcedLeray.B0296.gradHeatKernel2 1 w).2‖) *
        (1 + w.2 ^ 2) ^ (m / 2)) := by ring

/-- The heat kernel multiplied by the axial weight is integrable at each positive age. -/
theorem integrable_heatKernel1_mul_axialWeight {θ m : ℝ} (hθ : 0 < θ) (hm : 0 ≤ m) :
    Integrable (fun x : ℝ => UnforcedLeray.B0191.heatKernel 1 θ x *
      (1 + x ^ 2) ^ (m / 2)) := by
  let b := (4 * θ)⁻¹
  let C := (Real.sqrt (4 * Real.pi * 1 * θ))⁻¹
  have hb : 0 < b := by dsimp [b]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hbase := integrable_axialGaussianWeight hb hm
  have hmajor : Integrable (fun x : ℝ => C *
      ((1 + x ^ 2) ^ (m / 2) * Real.exp (-b * x ^ 2))) := by
    simpa [C, mul_comm] using hbase.const_mul C
  have hweight : Continuous (fun x : ℝ => (1 + x ^ 2) ^ (m / 2)) :=
    (Real.continuous_rpow_const (q := m / 2) (by linarith)).comp
      (continuous_const.add (continuous_id.pow 2))
  have hmeas : AEStronglyMeasurable
      (fun x : ℝ => UnforcedLeray.B0191.heatKernel 1 θ x * (1 + x ^ 2) ^ (m / 2)) volume :=
    (continuous_heatKernel1 θ).aestronglyMeasurable.mul hweight.aestronglyMeasurable
  refine hmajor.mono' hmeas ?_
  filter_upwards [] with x
  have hpos : 0 ≤ UnforcedLeray.B0191.heatKernel 1 θ x :=
    UnforcedLeray.B0191.heatKernel_pos one_pos hθ x |>.le
  have hw : 0 ≤ (1 + x ^ 2) ^ (m / 2) := Real.rpow_nonneg (by positivity) _
  have hf : 0 ≤ UnforcedLeray.B0191.heatKernel 1 θ x * (1 + x ^ 2) ^ (m / 2) :=
    mul_nonneg hpos hw
  exact le_of_eq (calc
    ‖UnforcedLeray.B0191.heatKernel 1 θ x * (1 + x ^ 2) ^ (m / 2)‖ =
        UnforcedLeray.B0191.heatKernel 1 θ x * (1 + x ^ 2) ^ (m / 2) := by
          rw [Real.norm_eq_abs, abs_of_nonneg hf]
    _ = C * ((1 + x ^ 2) ^ (m / 2) * Real.exp (-b * x ^ 2)) := by
          unfold C b UnforcedLeray.B0191.heatKernel
          have he : -x ^ 2 / (4 * 1 * θ) = -((4 * 1 * θ)⁻¹) * x ^ 2 := by
            field_simp
          rw [he]
          ring)

/-- The same weighted Gaussian with one derivative factor is integrable. -/
theorem integrable_abs_mul_axialGaussianWeight {b m : ℝ} (hb : 0 < b) (hm : 0 ≤ m) :
    Integrable (fun x : ℝ => |x| * (1 + x ^ 2) ^ (m / 2) * Real.exp (-b * x ^ 2)) := by
  let α := m / 2
  have hα : 0 ≤ α := by dsimp [α]; linarith
  have hzero : Integrable (fun x : ℝ => Real.exp (-b * x ^ 2)) := integrable_exp_neg_mul_sq hb
  have hmoment := integrable_sq_rpow_mul_gaussian hb (by linarith : 0 ≤ α + 1)
  have hsum : Integrable (fun x : ℝ =>
      Real.exp (-b * x ^ 2) + (x ^ 2) ^ (α + 1) * Real.exp (-b * x ^ 2)) := hzero.add hmoment
  have hmajor : Integrable (fun x : ℝ => 2 ^ α * 4 *
      (Real.exp (-b * x ^ 2) + (x ^ 2) ^ (α + 1) * Real.exp (-b * x ^ 2))) := by
    simpa [mul_assoc] using hsum.const_mul (2 ^ α * 4)
  refine hmajor.mono' ?_ ?_
  · fun_prop
  · filter_upwards [] with x
    have ht : 0 ≤ x ^ 2 := sq_nonneg x
    have hbase : (1 + x ^ 2) ^ α ≤ 2 ^ α * (1 + (x ^ 2) ^ α) := by
      have h1 : 1 + x ^ 2 ≤ 2 * max 1 (x ^ 2) := by
        have hL := le_max_left (1 : ℝ) (x ^ 2)
        have hR := le_max_right (1 : ℝ) (x ^ 2)
        nlinarith
      calc
        (1 + x ^ 2) ^ α ≤ (2 * max 1 (x ^ 2)) ^ α :=
          Real.rpow_le_rpow (by positivity) h1 hα
        _ = 2 ^ α * (max 1 (x ^ 2)) ^ α := by
          rw [Real.mul_rpow (by norm_num) (by positivity)]
        _ ≤ 2 ^ α * (1 + (x ^ 2) ^ α) := by
          have hmax : (max 1 (x ^ 2)) ^ α = max 1 ((x ^ 2) ^ α) := by
            have h := Real.rpow_max (x := (1 : ℝ)) (y := x ^ 2) (p := α)
              (by norm_num) ht hα
            simpa using h
          rw [hmax]
          have hy : 0 ≤ (x ^ 2) ^ α := Real.rpow_nonneg ht α
          have hle : max 1 ((x ^ 2) ^ α) ≤ 1 + (x ^ 2) ^ α :=
            max_le (by linarith [hy]) (by linarith)
          exact mul_le_mul_of_nonneg_left hle (by positivity)
    have hmul : |x| * (1 + (x ^ 2) ^ α) ≤ 4 * (1 + (x ^ 2) ^ (α + 1)) := by
      let t := x ^ 2
      have ht0 : 0 ≤ t := by dsimp [t]; positivity
      have hx : |x| ≤ 1 + t := by
        dsimp [t]
        nlinarith [sq_abs x]
      have hαt : 0 ≤ t ^ α := Real.rpow_nonneg ht0 α
      have hpower : 0 ≤ t ^ (α + 1) := Real.rpow_nonneg ht0 (α + 1)
      have htα : t ^ α ≤ 1 + t ^ (α + 1) := by
        by_cases ht1 : t ≤ 1
        · have hle : t ^ α ≤ 1 ^ α := Real.rpow_le_rpow ht0 ht1 hα
          have hone : (1 : ℝ) ^ α = 1 := Real.one_rpow α
          rw [hone] at hle
          linarith [hpower]
        · have ht1' : 1 ≤ t := le_of_not_ge ht1
          have hle : t ^ α ≤ t ^ (α + 1) := by
            apply Real.rpow_le_rpow_of_exponent_le ht1'
            linarith
          linarith
      have htlin : t ≤ 1 + t ^ (α + 1) := by
        by_cases ht1 : t ≤ 1
        · linarith
        · have ht1' : 1 ≤ t := le_of_not_ge ht1
          have hle : t ≤ t ^ (α + 1) := by
            calc
              t = t ^ (1 : ℝ) := by rw [Real.rpow_one]
              _ ≤ t ^ (α + 1) := Real.rpow_le_rpow_of_exponent_le ht1' (by linarith)
          linarith
      have hsum : (1 + t) * (1 + t ^ α) ≤ 4 * (1 + t ^ (α + 1)) := by
        have hprod : (1 + t) * (1 + t ^ α) = 1 + t + t ^ α + t * t ^ α := by ring
        rw [hprod]
        have hlast : t * t ^ α = t ^ (α + 1) := by
          by_cases hz : t = 0
          · simp [hz, Real.zero_rpow (by linarith : α + 1 ≠ 0)]
          · have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm hz)
            calc
              t * t ^ α = t ^ (1 : ℝ) * t ^ α := by rw [Real.rpow_one]
              _ = t ^ (1 + α) := by rw [← Real.rpow_add htpos]
              _ = t ^ (α + 1) := by rw [show (1 : ℝ) + α = α + 1 by ring]
        rw [hlast]
        linarith
      calc
        |x| * (1 + t ^ α) ≤ (1 + t) * (1 + t ^ α) :=
          mul_le_mul_of_nonneg_right hx (by positivity)
        _ ≤ 4 * (1 + t ^ (α + 1)) := hsum
    have hleft : 0 ≤ |x| * (1 + x ^ 2) ^ α * Real.exp (-b * x ^ 2) := by positivity
    have hright : 0 ≤ 2 ^ α * 4 *
        (Real.exp (-b * x ^ 2) + (x ^ 2) ^ (α + 1) * Real.exp (-b * x ^ 2)) := by positivity
    calc
      ‖|x| * (1 + x ^ 2) ^ α * Real.exp (-b * x ^ 2)‖ =
          |x| * (1 + x ^ 2) ^ α * Real.exp (-b * x ^ 2) := by
            rw [Real.norm_eq_abs, abs_of_nonneg hleft]
      _ ≤ (2 ^ α * (|x| * (1 + (x ^ 2) ^ α))) * Real.exp (-b * x ^ 2) :=
            mul_le_mul_of_nonneg_right
              (calc
                |x| * (1 + x ^ 2) ^ α ≤ |x| * (2 ^ α * (1 + (x ^ 2) ^ α)) :=
                  mul_le_mul_of_nonneg_left hbase (abs_nonneg x)
                _ = 2 ^ α * (|x| * (1 + (x ^ 2) ^ α)) := by ring)
              (Real.exp_pos _).le
      _ ≤ (2 ^ α * (4 * (1 + (x ^ 2) ^ (α + 1)))) * Real.exp (-b * x ^ 2) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hmul (by positivity)) (Real.exp_pos _).le
      _ = 2 ^ α * 4 * (1 + (x ^ 2) ^ (α + 1)) * Real.exp (-b * x ^ 2) := by ring
      _ = 2 ^ α * 4 *
          (Real.exp (-b * x ^ 2) + (x ^ 2) ^ (α + 1) * Real.exp (-b * x ^ 2)) := by ring

/-- The heat derivative multiplied by the axial weight is integrable at each positive age. -/
theorem integrable_dHeatKernel_mul_axialWeight {θ m : ℝ} (hθ : 0 < θ) (hm : 0 ≤ m) :
    Integrable (fun x : ℝ => UnforcedLeray.B0296.dHeatKernel θ x *
      (1 + x ^ 2) ^ (m / 2)) := by
  let b := (4 * 1 * θ)⁻¹
  let C := (2 * θ)⁻¹ * (Real.sqrt (4 * Real.pi * 1 * θ))⁻¹
  have hb : 0 < b := by dsimp [b]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hbase := integrable_abs_mul_axialGaussianWeight hb hm
  have hmajor : Integrable (fun x : ℝ => C *
      (|x| * (1 + x ^ 2) ^ (m / 2) * Real.exp (-b * x ^ 2))) := by
    simpa [C, mul_comm, mul_left_comm, mul_assoc] using hbase.const_mul C
  have hweight : Continuous (fun x : ℝ => (1 + x ^ 2) ^ (m / 2)) :=
    (Real.continuous_rpow_const (q := m / 2) (by linarith)).comp
      (continuous_const.add (continuous_id.pow 2))
  have hmeas : AEStronglyMeasurable
      (fun x : ℝ => UnforcedLeray.B0296.dHeatKernel θ x * (1 + x ^ 2) ^ (m / 2)) volume :=
    (measurable_dHeatKernel θ).aestronglyMeasurable.mul hweight.aestronglyMeasurable
  refine hmajor.mono' hmeas ?_
  filter_upwards [] with x
  have hw : 0 ≤ (1 + x ^ 2) ^ (m / 2) := Real.rpow_nonneg (by positivity) _
  have hformula := UnforcedLeray.B0296.abs_dHeatKernel hθ x
  exact le_of_eq (calc
    ‖UnforcedLeray.B0296.dHeatKernel θ x * (1 + x ^ 2) ^ (m / 2)‖ =
        |UnforcedLeray.B0296.dHeatKernel θ x| * (1 + x ^ 2) ^ (m / 2) := by
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw]
    _ = C * (|x| * (1 + x ^ 2) ^ (m / 2) * Real.exp (-b * x ^ 2)) := by
          rw [hformula]
          unfold C b
          ring)


/-- The actual planar heat-gradient kernel is integrable after multiplication by the
q-independent axial weight. This is the fixed-cylinder kernel-moment input for weighted Young. -/
theorem integrable_gradKernelNorm_mul_axialWeight {θ m : ℝ} (hθ : 0 < θ) (hm : 0 ≤ m) :
    Integrable (fun w : Plane =>
      (‖(UnforcedLeray.B0296.gradHeatKernel2 θ w).1‖ +
        ‖(UnforcedLeray.B0296.gradHeatKernel2 θ w).2‖) *
        (1 + w.2 ^ 2) ^ (m / 2)) := by
  let f := fun x : ℝ => ‖UnforcedLeray.B0296.dHeatKernel θ x‖
  let g := fun x : ℝ => UnforcedLeray.B0191.heatKernel 1 θ x * (1 + x ^ 2) ^ (m / 2)
  let h := fun x : ℝ => ‖UnforcedLeray.B0191.heatKernel 1 θ x‖
  let k := fun x : ℝ => ‖UnforcedLeray.B0296.dHeatKernel θ x * (1 + x ^ 2) ^ (m / 2)‖
  have hf : Integrable f := by
    simpa [f] using (UnforcedLeray.B0296.integrable_dHeatKernel hθ).norm
  have hg : Integrable g := by simpa [g] using integrable_heatKernel1_mul_axialWeight hθ hm
  have hh : Integrable h := by
    simpa [h] using (UnforcedLeray.B0296.integrable_heatKernel1 hθ).norm
  have hk : Integrable k := by
    simpa [k] using (integrable_dHeatKernel_mul_axialWeight hθ hm).norm
  have hfirst : Integrable (fun w : Plane => f w.1 * g w.2) := hf.mul_prod hg
  have hsecond : Integrable (fun w : Plane => h w.1 * k w.2) := hh.mul_prod hk
  have hsum : Integrable (fun w : Plane => f w.1 * g w.2 + h w.1 * k w.2) :=
    hfirst.add hsecond
  refine hsum.congr (Eventually.of_forall fun w => ?_)
  have hweight : 0 ≤ (1 + w.2 ^ 2) ^ (m / 2) := Real.rpow_nonneg (by positivity) _
  have hheat : 0 ≤ UnforcedLeray.B0191.heatKernel 1 θ w.2 :=
    (UnforcedLeray.B0191.heatKernel_pos one_pos hθ w.2).le
  have hheatq : 0 ≤ UnforcedLeray.B0191.heatKernel 1 θ w.1 :=
    (UnforcedLeray.B0191.heatKernel_pos one_pos hθ w.1).le
  simp [f, g, h, k, UnforcedLeray.B0296.gradHeatKernel2, norm_mul,
    Real.norm_eq_abs, abs_of_nonneg hheat, abs_of_nonneg hheatq,
    abs_of_nonneg hweight, mul_assoc, mul_left_comm, mul_comm]
  <;> ring

/-- The actual weighted gradient moment is bounded by its unit-age value times
`θ^(-1/2)` on the unit strip. The constant is the explicit finite integral at age one. -/
theorem integral_gradKernelAxialMoment_le {θ m : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hm : 0 ≤ m) :
    ∫ w : Plane, gradKernelAxialMomentDensity θ m w ≤
      θ ^ (-(1 / 2 : ℝ)) * ∫ w : Plane, gradKernelAxialMomentDensity 1 m w := by
  let r := Real.sqrt θ
  have hr : 0 < r := by dsimp [r]; exact Real.sqrt_pos.2 hθ
  have hr2 : r ^ 2 = θ := by dsimp [r]; exact Real.sq_sqrt hθ.le
  have hr2le : r ^ 2 ≤ 1 := by rw [hr2]; exact hθ1
  have hθmem : Integrable (fun w : Plane => gradKernelAxialMomentDensity θ m w) := by
    simpa [gradKernelAxialMomentDensity] using
      integrable_gradKernelNorm_mul_axialWeight hθ hm
  have h1mem : Integrable (fun w : Plane => gradKernelAxialMomentDensity 1 m w) := by
    simpa [gradKernelAxialMomentDensity] using
      integrable_gradKernelNorm_mul_axialWeight one_pos hm
  have hcomp : Integrable (fun w : Plane => gradKernelAxialMomentDensity θ m (r • w)) := by
    exact (integrable_comp_smul_iff volume
      (fun w : Plane => gradKernelAxialMomentDensity θ m w) hr.ne').2 hθmem
  have hmajor : Integrable (fun w : Plane => (r ^ 3)⁻¹ *
      gradKernelAxialMomentDensity 1 m w) := by
    simpa [mul_comm] using h1mem.const_mul ((r ^ 3)⁻¹)
  have hmono : ∫ w : Plane, gradKernelAxialMomentDensity θ m (r • w) ≤
      ∫ w : Plane, (r ^ 3)⁻¹ * gradKernelAxialMomentDensity 1 m w :=
    integral_mono hcomp hmajor (fun w => by
      simpa [hr2] using gradKernelAxialMomentDensity_scale_le hr hr2le hm w)
  have hchange := MeasureTheory.Measure.integral_comp_smul (volume : Measure Plane)
    (fun w : Plane => gradKernelAxialMomentDensity θ m w) r
  have hdim : Module.finrank ℝ Plane = 2 := by simp [Plane, Module.finrank_prod]
  rw [hdim] at hchange
  have hchange' : ∫ w : Plane, gradKernelAxialMomentDensity θ m (r • w) =
      (r ^ 2)⁻¹ * ∫ w : Plane, gradKernelAxialMomentDensity θ m w := by
    simpa [abs_of_pos hr, smul_eq_mul, Real.rpow_neg hr.le, Real.rpow_natCast] using hchange
  have hsolve : ∫ w : Plane, gradKernelAxialMomentDensity θ m w =
      r ^ 2 * ∫ w : Plane, gradKernelAxialMomentDensity θ m (r • w) := by
    rw [hchange']
    field_simp
  have hscale : ∫ w : Plane, gradKernelAxialMomentDensity θ m w ≤
      r⁻¹ * ∫ w : Plane, gradKernelAxialMomentDensity 1 m w := by
    calc
      ∫ w : Plane, gradKernelAxialMomentDensity θ m w =
          r ^ 2 * ∫ w : Plane, gradKernelAxialMomentDensity θ m (r • w) := hsolve
      _ ≤ r ^ 2 * ∫ w : Plane, (r ^ 3)⁻¹ *
          gradKernelAxialMomentDensity 1 m w :=
        mul_le_mul_of_nonneg_left hmono (sq_nonneg r)
      _ = r⁻¹ * ∫ w : Plane, gradKernelAxialMomentDensity 1 m w := by
        rw [integral_const_mul]
        field_simp
  have hrInv : r⁻¹ = θ ^ (-(1 / 2 : ℝ)) := by
    dsimp [r]
    rw [Real.rpow_neg hθ.le, ← Real.sqrt_eq_rpow]
  rw [← hrInv]
  exact hscale


#print axioms integrable_sq_rpow_mul_gaussian
#print axioms integrable_axialGaussianWeight
#print axioms integrable_abs_mul_axialGaussianWeight
#print axioms integrable_heatKernel1_mul_axialWeight
#print axioms integrable_dHeatKernel_mul_axialWeight
#print axioms integrable_gradKernelNorm_mul_axialWeight
#print axioms heatKernel_scale_sqr
#print axioms dHeatKernel_scale_sqr
#print axioms gradHeatKernel2_scale_sqr
#print axioms gradKernelAxialMomentDensity_scale_le
#print axioms integral_gradKernelAxialMoment_le

end UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution
