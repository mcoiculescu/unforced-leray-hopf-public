import UnforcedLeray.Lib.HeatCylinder.OrbitBounds

/-!
# Compact-positive-time Gaussian-gradient majorant

On `a ≤ θ ≤ b`, the Gaussian gradient is bounded by `(b/a)^2` times its value at time `b`.
This is the integrable envelope needed for dominated continuity of the kernel parameter.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.GaussianVortex (Plane)

private def gradKernelPrefactor (θ : ℝ) : ℝ :=
  (2 * θ)⁻¹ * (Real.sqrt (4 * Real.pi * 1 * θ))⁻¹ ^ 2

private theorem gradKernelPrefactor_eq {θ : ℝ} (hθ : 0 < θ) :
    gradKernelPrefactor θ = (8 * Real.pi * θ ^ 2)⁻¹ := by
  unfold gradKernelPrefactor
  have hs : (Real.sqrt (4 * Real.pi * 1 * θ))⁻¹ ^ 2 =
      (4 * Real.pi * 1 * θ)⁻¹ := by
    have hs0 : Real.sqrt (4 * Real.pi * 1 * θ) ≠ 0 := by positivity
    field_simp [hs0]
    rw [Real.sq_sqrt (by positivity)]
  rw [hs]
  field_simp
  <;> ring

private theorem gradKernelPrefactor_le {a θ b : ℝ} (ha : 0 < a) (hθ : 0 < θ)
    (hb : 0 < b) (haθ : a ≤ θ) (hθb : θ ≤ b) :
    gradKernelPrefactor θ ≤ (b / a) ^ 2 * gradKernelPrefactor b := by
  rw [gradKernelPrefactor_eq hθ, gradKernelPrefactor_eq hb]
  have hratio : (b / a) ^ 2 * (8 * Real.pi * b ^ 2)⁻¹ =
      (8 * Real.pi * a ^ 2)⁻¹ := by
    field_simp [ha.ne', hb.ne', Real.pi_ne_zero]
    <;> ring
  rw [hratio]
  have hden : 8 * Real.pi * a ^ 2 ≤ 8 * Real.pi * θ ^ 2 := by gcongr
  simpa [one_div] using one_div_le_one_div_of_le (by positivity) hden

private theorem gradHeatKernel2_fst_explicit {θ : ℝ} (hθ : 0 < θ) (w : Plane) :
    (UnforcedLeray.B0296.gradHeatKernel2 θ w).1 =
      -(w.1 / (2 * θ)) * (Real.sqrt (4 * Real.pi * 1 * θ))⁻¹ ^ 2 *
        Real.exp (-(w.1 ^ 2 / (4 * θ))) * Real.exp (-(w.2 ^ 2 / (4 * θ))) := by
  unfold UnforcedLeray.B0296.gradHeatKernel2 UnforcedLeray.B0296.dHeatKernel
    UnforcedLeray.B0191.heatKernel
  have hs : Real.sqrt (4 * Real.pi * 1 * θ) ≠ 0 := by positivity
  field_simp [hs]

private theorem gradHeatKernel2_snd_explicit {θ : ℝ} (hθ : 0 < θ) (w : Plane) :
    (UnforcedLeray.B0296.gradHeatKernel2 θ w).2 =
      -(w.2 / (2 * θ)) * (Real.sqrt (4 * Real.pi * 1 * θ))⁻¹ ^ 2 *
        Real.exp (-(w.1 ^ 2 / (4 * θ))) * Real.exp (-(w.2 ^ 2 / (4 * θ))) := by
  unfold UnforcedLeray.B0296.gradHeatKernel2 UnforcedLeray.B0296.dHeatKernel
    UnforcedLeray.B0191.heatKernel
  have hs : Real.sqrt (4 * Real.pi * 1 * θ) ≠ 0 := by positivity
  field_simp [hs]

private theorem abs_gradHeatKernel2_fst_explicit {θ : ℝ} (hθ : 0 < θ) (w : Plane) :
    |(UnforcedLeray.B0296.gradHeatKernel2 θ w).1| =
      (|w.1| / (2 * θ)) * (Real.sqrt (4 * Real.pi * 1 * θ))⁻¹ ^ 2 *
        Real.exp (-(w.1 ^ 2 / (4 * θ))) * Real.exp (-(w.2 ^ 2 / (4 * θ))) := by
  rw [gradHeatKernel2_fst_explicit hθ]
  have hs : 0 < Real.sqrt (4 * Real.pi * 1 * θ) := by positivity
  have hden : 0 < 2 * θ := by positivity
  simp [abs_mul, abs_div, abs_of_pos hs, abs_of_pos hden, Real.exp_pos]

private theorem abs_gradHeatKernel2_snd_explicit {θ : ℝ} (hθ : 0 < θ) (w : Plane) :
    |(UnforcedLeray.B0296.gradHeatKernel2 θ w).2| =
      (|w.2| / (2 * θ)) * (Real.sqrt (4 * Real.pi * 1 * θ))⁻¹ ^ 2 *
        Real.exp (-(w.1 ^ 2 / (4 * θ))) * Real.exp (-(w.2 ^ 2 / (4 * θ))) := by
  rw [gradHeatKernel2_snd_explicit hθ]
  have hs : 0 < Real.sqrt (4 * Real.pi * 1 * θ) := by positivity
  have hden : 0 < 2 * θ := by positivity
  simp [abs_mul, abs_div, abs_of_pos hs, abs_of_pos hden, Real.exp_pos]

private theorem exp_heatAge_le {θ b x : ℝ} (hθ : 0 < θ) (hb : 0 < b)
    (hθb : θ ≤ b) :
    Real.exp (-(x ^ 2 / (4 * θ))) ≤ Real.exp (-(x ^ 2 / (4 * b))) := by
  apply Real.exp_le_exp.mpr
  apply neg_le_neg
  have hden : 4 * θ ≤ 4 * b := by nlinarith
  have hrecip : 1 / (4 * b) ≤ 1 / (4 * θ) :=
    one_div_le_one_div_of_le (by positivity) hden
  have hmul : x ^ 2 * (1 / (4 * b)) ≤ x ^ 2 * (1 / (4 * θ)) :=
    mul_le_mul_of_nonneg_left hrecip (sq_nonneg x)
  simpa [div_eq_mul_inv, mul_comm] using hmul

private theorem abs_gradHeatKernel2_fst_le {a θ b : ℝ} (ha : 0 < a) (hθ : 0 < θ)
    (hb : 0 < b) (haθ : a ≤ θ) (hθb : θ ≤ b) (w : Plane) :
    |(UnforcedLeray.B0296.gradHeatKernel2 θ w).1| ≤
      (b / a) ^ 2 * |(UnforcedLeray.B0296.gradHeatKernel2 b w).1| := by
  rw [abs_gradHeatKernel2_fst_explicit hθ w,
    abs_gradHeatKernel2_fst_explicit hb w]
  have hpref := gradKernelPrefactor_le ha hθ hb haθ hθb
  have hq : (|w.1| / (2 * θ)) *
      (Real.sqrt (4 * Real.pi * 1 * θ))⁻¹ ^ 2 =
      gradKernelPrefactor θ * |w.1| := by
    unfold gradKernelPrefactor
    ring
  have hqb : (|w.1| / (2 * b)) *
      (Real.sqrt (4 * Real.pi * 1 * b))⁻¹ ^ 2 =
      gradKernelPrefactor b * |w.1| := by
    unfold gradKernelPrefactor
    ring
  rw [hq, hqb]
  have he₁ := exp_heatAge_le hθ hb hθb (x := w.1)
  have he₂ := exp_heatAge_le hθ hb hθb (x := w.2)
  have hnonnegPref : 0 ≤ gradKernelPrefactor b := by
    unfold gradKernelPrefactor
    positivity
  have hnonnegX : 0 ≤ |w.1| := abs_nonneg _
  calc
    gradKernelPrefactor θ * |w.1| *
        Real.exp (-(w.1 ^ 2 / (4 * θ))) * Real.exp (-(w.2 ^ 2 / (4 * θ))) ≤
      ((b / a) ^ 2 * gradKernelPrefactor b) * |w.1| *
        Real.exp (-(w.1 ^ 2 / (4 * θ))) * Real.exp (-(w.2 ^ 2 / (4 * θ))) := by
          gcongr
    _ ≤ ((b / a) ^ 2 * gradKernelPrefactor b) * |w.1| *
        Real.exp (-(w.1 ^ 2 / (4 * b))) * Real.exp (-(w.2 ^ 2 / (4 * b))) := by
          gcongr
    _ = (b / a) ^ 2 * (gradKernelPrefactor b * |w.1| *
        Real.exp (-(w.1 ^ 2 / (4 * b))) * Real.exp (-(w.2 ^ 2 / (4 * b)))) := by ring

private theorem abs_gradHeatKernel2_snd_le {a θ b : ℝ} (ha : 0 < a) (hθ : 0 < θ)
    (hb : 0 < b) (haθ : a ≤ θ) (hθb : θ ≤ b) (w : Plane) :
    |(UnforcedLeray.B0296.gradHeatKernel2 θ w).2| ≤
      (b / a) ^ 2 * |(UnforcedLeray.B0296.gradHeatKernel2 b w).2| := by
  rw [abs_gradHeatKernel2_snd_explicit hθ w,
    abs_gradHeatKernel2_snd_explicit hb w]
  have hpref := gradKernelPrefactor_le ha hθ hb haθ hθb
  have hq : (|w.2| / (2 * θ)) *
      (Real.sqrt (4 * Real.pi * 1 * θ))⁻¹ ^ 2 =
      gradKernelPrefactor θ * |w.2| := by
    unfold gradKernelPrefactor
    ring
  have hqb : (|w.2| / (2 * b)) *
      (Real.sqrt (4 * Real.pi * 1 * b))⁻¹ ^ 2 =
      gradKernelPrefactor b * |w.2| := by
    unfold gradKernelPrefactor
    ring
  rw [hq, hqb]
  have he₁ := exp_heatAge_le hθ hb hθb (x := w.1)
  have he₂ := exp_heatAge_le hθ hb hθb (x := w.2)
  have heprod := mul_le_mul he₁ he₂ (Real.exp_nonneg _) (Real.exp_nonneg _)
  have hcoefnn : 0 ≤ ((b / a) ^ 2 * gradKernelPrefactor b) * |w.2| := by
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (by
      unfold gradKernelPrefactor
      positivity)) (abs_nonneg _)
  calc
    gradKernelPrefactor θ * |w.2| *
        Real.exp (-(w.1 ^ 2 / (4 * θ))) * Real.exp (-(w.2 ^ 2 / (4 * θ))) ≤
      ((b / a) ^ 2 * gradKernelPrefactor b) * |w.2| *
        Real.exp (-(w.1 ^ 2 / (4 * θ))) * Real.exp (-(w.2 ^ 2 / (4 * θ))) := by
          gcongr <;> positivity
    _ ≤ ((b / a) ^ 2 * gradKernelPrefactor b) * |w.2| *
        Real.exp (-(w.1 ^ 2 / (4 * b))) * Real.exp (-(w.2 ^ 2 / (4 * b))) := by
          calc
            _ = (((b / a) ^ 2 * gradKernelPrefactor b) * |w.2|) *
                (Real.exp (-(w.1 ^ 2 / (4 * θ))) *
                  Real.exp (-(w.2 ^ 2 / (4 * θ)))) := by ring
            _ ≤ (((b / a) ^ 2 * gradKernelPrefactor b) * |w.2|) *
                (Real.exp (-(w.1 ^ 2 / (4 * b))) *
                  Real.exp (-(w.2 ^ 2 / (4 * b)))) :=
              mul_le_mul_of_nonneg_left heprod hcoefnn
            _ = _ := by ring
    _ = (b / a) ^ 2 * (gradKernelPrefactor b * |w.2| *
        Real.exp (-(w.1 ^ 2 / (4 * b))) * Real.exp (-(w.2 ^ 2 / (4 * b)))) := by ring

/-- The actual positive-time Gaussian gradient is dominated pointwise on a compact positive
time interval by its value at the upper endpoint, with the exact scaling factor `(b/a)^2`. -/
theorem gradKernelAbs_le_of_interval {a θ b : ℝ} (ha : 0 < a) (hθ : 0 < θ)
    (hb : 0 < b) (haθ : a ≤ θ) (hθb : θ ≤ b) (w : Plane) :
    UnforcedLeray.B0296.gradKernelAbs θ w ≤
      ENNReal.ofReal ((b / a) ^ 2) * UnforcedLeray.B0296.gradKernelAbs b w := by
  unfold UnforcedLeray.B0296.gradKernelAbs
  rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs,
    Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs]
  have hC : 0 ≤ (b / a) ^ 2 := sq_nonneg _
  have hq : ENNReal.ofReal |(UnforcedLeray.B0296.gradHeatKernel2 θ w).1| ≤
      ENNReal.ofReal ((b / a) ^ 2) *
        ENNReal.ofReal |(UnforcedLeray.B0296.gradHeatKernel2 b w).1| := by
    calc
      _ ≤ ENNReal.ofReal ((b / a) ^ 2 *
          |(UnforcedLeray.B0296.gradHeatKernel2 b w).1|) :=
        ENNReal.ofReal_le_ofReal (abs_gradHeatKernel2_fst_le ha hθ hb haθ hθb w)
      _ = _ := ENNReal.ofReal_mul hC
  have hη : ENNReal.ofReal |(UnforcedLeray.B0296.gradHeatKernel2 θ w).2| ≤
      ENNReal.ofReal ((b / a) ^ 2) *
        ENNReal.ofReal |(UnforcedLeray.B0296.gradHeatKernel2 b w).2| := by
    calc
      _ ≤ ENNReal.ofReal ((b / a) ^ 2 *
          |(UnforcedLeray.B0296.gradHeatKernel2 b w).2|) :=
        ENNReal.ofReal_le_ofReal (abs_gradHeatKernel2_snd_le ha hθ hb haθ hθb w)
      _ = _ := ENNReal.ofReal_mul hC
  calc
    ENNReal.ofReal |(UnforcedLeray.B0296.gradHeatKernel2 θ w).1| +
        ENNReal.ofReal |(UnforcedLeray.B0296.gradHeatKernel2 θ w).2| ≤
      ENNReal.ofReal ((b / a) ^ 2) *
          ENNReal.ofReal |(UnforcedLeray.B0296.gradHeatKernel2 b w).1| +
        ENNReal.ofReal ((b / a) ^ 2) *
          ENNReal.ofReal |(UnforcedLeray.B0296.gradHeatKernel2 b w).2| := add_le_add hq hη
    _ = ENNReal.ofReal ((b / a) ^ 2) *
        (ENNReal.ofReal |(UnforcedLeray.B0296.gradHeatKernel2 b w).1| +
          ENNReal.ofReal |(UnforcedLeray.B0296.gradHeatKernel2 b w).2|) := by rw [← mul_add]

end UnforcedLeray.HeatCylinder
