import UnforcedLeray.Short.PartIIIa.Clock.Moving
import UnforcedLeray.Short.PartIIIa.Clock.LongAssemble.H1

/-!
# Part III-a long assembly, H2: monotonicity of `FrameStable` and `FrameAmplitude` in the constant `C`

If `|C| ≤ C'` then the stable convolution and the amplitude inequality with constant `C` imply the
same with `C'`. This lets the Gronwall step use a positive constant.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

lemma frameStable_mono (P : PlanarData) {ν m b K : ℝ} (F : MovingFrame ν (ν ^ (-2 : ℝ)) m b K)
    {C C' h₀ : ℝ} (hν : 0 < ν) (hC : |C| ≤ C') (hF : FrameStable P F C h₀) :
    FrameStable P F C' h₀ := by
  intro tr htr t s ht hts hb f w u hw hz
  obtain ⟨h1, h2, h3⟩ := hF tr htr t s ht hts hb f w u hw hz
  refine ⟨h1, h2, le_trans h3 ?_⟩
  have hCC : C ≤ C' := le_trans (le_abs_self C) hC
  have hs0 : 0 ≤ s := le_trans ht hts
  have hY : 0 ≤ (1 + ν ^ 3) / clockTheta ν s :=
    div_nonneg (by positivity) (theta_pos hν hs0).le
  have hCC2 : C * C ≤ C' * C' := by
    have h0 : |C| * |C| ≤ C' * C' := mul_le_mul hC hC (abs_nonneg C) (le_trans (abs_nonneg C) hC)
    rwa [abs_mul_abs_self] at h0
  refine mul_le_mul_of_nonneg_left ?_ zero_le
  apply add_le_add
  · refine mul_le_mul_of_nonneg_right ?_ zero_le
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_right hCC (Real.exp_pos _).le
  · refine mul_le_mul_of_nonneg_right ?_ zero_le
    apply ENNReal.ofReal_le_ofReal
    calc C * (C * (1 + ν ^ 3) / clockTheta ν s)
        = (C * C) * ((1 + ν ^ 3) / clockTheta ν s) := by ring
      _ ≤ (C' * C') * ((1 + ν ^ 3) / clockTheta ν s) := mul_le_mul_of_nonneg_right hCC2 hY
      _ = C' * (C' * (1 + ν ^ 3) / clockTheta ν s) := by ring

lemma frameAmp_mono (P : PlanarData) {ν m b K : ℝ} (F : MovingFrame ν (ν ^ (-2 : ℝ)) m b K)
    {C C' : ℝ} (hν : 0 < ν) (hC : |C| ≤ C') (hF : FrameAmplitude P F C) :
    FrameAmplitude P F C' := by
  intro tr htr t s ht hts hb f w u hw hz
  refine le_trans (hF tr htr t s ht hts hb f w u hw hz) ?_
  have hCC : C ≤ C' := le_trans (le_abs_self C) hC
  have hCC2 : C * C ≤ C' * C' := by
    have h0 : |C| * |C| ≤ C' * C' := mul_le_mul hC hC (abs_nonneg C) (le_trans (abs_nonneg C) hC)
    rwa [abs_mul_abs_self] at h0
  refine add_le_add le_rfl (setLIntegral_mono' measurableSet_Ioc (fun r hr => ?_))
  have hr0 : 0 ≤ r := le_trans ht (le_of_lt hr.1)
  have hθ : 0 < clockTheta ν r := theta_pos hν hr0
  have hp : 0 ≤ ν ^ 3 / clockTheta ν r := div_nonneg (pow_nonneg hν.le 3) hθ.le
  have hq : 0 ≤ 1 / clockTheta ν r := div_nonneg zero_le_one hθ.le
  refine mul_le_mul_of_nonneg_left ?_ zero_le
  apply add_le_add
  · refine mul_le_mul_of_nonneg_right ?_ zero_le
    apply ENNReal.ofReal_le_ofReal
    have : C * ν ^ 3 / clockTheta ν r = C * (ν ^ 3 / clockTheta ν r) := by ring
    have h2 : C' * ν ^ 3 / clockTheta ν r = C' * (ν ^ 3 / clockTheta ν r) := by ring
    rw [this, h2]
    exact mul_le_mul_of_nonneg_right hCC hp
  · refine mul_le_mul_of_nonneg_right ?_ zero_le
    apply ENNReal.ofReal_le_ofReal
    have e1 : C * (1 / clockTheta ν r + C * ν ^ 3 / clockTheta ν r)
        = C * (1 / clockTheta ν r) + (C * C) * (ν ^ 3 / clockTheta ν r) := by ring
    have e2 : C' * (1 / clockTheta ν r + C' * ν ^ 3 / clockTheta ν r)
        = C' * (1 / clockTheta ν r) + (C' * C') * (ν ^ 3 / clockTheta ν r) := by ring
    rw [e1, e2]
    have h3 := mul_le_mul_of_nonneg_right hCC hq
    have h4 := mul_le_mul_of_nonneg_right hCC2 hp
    linarith

end UnforcedLeray.Short.IIIa
