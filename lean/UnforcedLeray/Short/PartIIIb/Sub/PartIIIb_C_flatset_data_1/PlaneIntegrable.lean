import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_data_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_data_1.GaussPointBound
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_data_1.GaussMeasurable
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Prod

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- Weight comparison `(1+ρ)² e^{-ρ/(4a)} ≤ (1+16a)² e^{-ρ/(8a)}` for `ρ ≥ 0`, `a > 0`. -/
theorem pi_weight (a ρ : ℝ) (ha : 0 < a) (hρ : 0 ≤ ρ) :
    (1 + ρ) ^ 2 * Real.exp (-ρ / (4 * a)) ≤ (1 + 16 * a) ^ 2 * Real.exp (-ρ / (8 * a)) := by
  have ha16 : (0 : ℝ) < 16 * a := by linarith
  have ht : 0 ≤ ρ / (16 * a) := div_nonneg hρ ha16.le
  have h1 := Real.add_one_le_exp (ρ / (16 * a))
  have h2 : ρ / (16 * a) * (16 * a) = ρ := div_mul_cancel₀ ρ ha16.ne'
  have hE1 : 1 + ρ ≤ (1 + 16 * a) * Real.exp (ρ / (16 * a)) := by
    have hpos : (0 : ℝ) ≤ 1 + 16 * a := by linarith
    nlinarith [mul_nonneg hpos (sub_nonneg.2 h1), h2, ht, ha]
  have hsq : (1 + ρ) ^ 2 ≤ ((1 + 16 * a) * Real.exp (ρ / (16 * a))) ^ 2 :=
    pow_le_pow_left₀ (by linarith) hE1 2
  have hE : Real.exp (ρ / (16 * a)) * Real.exp (ρ / (16 * a)) * Real.exp (-ρ / (4 * a))
      = Real.exp (-ρ / (8 * a)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hEpos : 0 ≤ Real.exp (-ρ / (4 * a)) := (Real.exp_pos _).le
  calc (1 + ρ) ^ 2 * Real.exp (-ρ / (4 * a))
      ≤ ((1 + 16 * a) * Real.exp (ρ / (16 * a))) ^ 2 * Real.exp (-ρ / (4 * a)) :=
        mul_le_mul_of_nonneg_right hsq hEpos
    _ = (1 + 16 * a) ^ 2 * (Real.exp (ρ / (16 * a)) * Real.exp (ρ / (16 * a)) *
          Real.exp (-ρ / (4 * a))) := by ring
    _ = (1 + 16 * a) ^ 2 * Real.exp (-ρ / (8 * a)) := by rw [hE]

/-- One bound of a source profile by the separable Gaussian majorant. -/
theorem pi_bound (a C : ℝ) (ha : 1 ≤ a) (hC0 : 0 ≤ C) (x : ℝ × ℝ) (y : ℝ)
    (hy : y ≤ C * (1 + x.1 ^ 2 + x.2 ^ 2) ^ 2 * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (4 * a))) :
    y ≤ C * (1 + 16 * a) ^ 2 *
      (Real.exp (-(1 / (8 * a)) * x.1 ^ 2) * Real.exp (-(1 / (8 * a)) * x.2 ^ 2)) := by
  have e : 1 + x.1 ^ 2 + x.2 ^ 2 = 1 + (x.1 ^ 2 + x.2 ^ 2) := by ring
  rw [e] at hy
  have hρ : 0 ≤ x.1 ^ 2 + x.2 ^ 2 := by positivity
  have hw := pi_weight a (x.1 ^ 2 + x.2 ^ 2) (by linarith) hρ
  have hexp : Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (8 * a)) =
      Real.exp (-(1 / (8 * a)) * x.1 ^ 2) * Real.exp (-(1 / (8 * a)) * x.2 ^ 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc y ≤ C * (1 + (x.1 ^ 2 + x.2 ^ 2)) ^ 2 * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (4 * a)) := hy
    _ = C * ((1 + (x.1 ^ 2 + x.2 ^ 2)) ^ 2 * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (4 * a))) := by
        ring
    _ ≤ C * ((1 + 16 * a) ^ 2 * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (8 * a))) :=
        mul_le_mul_of_nonneg_left hw hC0
    _ = C * (1 + 16 * a) ^ 2 *
        (Real.exp (-(1 / (8 * a)) * x.1 ^ 2) * Real.exp (-(1 / (8 * a)) * x.2 ^ 2)) := by
        rw [hexp]
        ring

/-- **The source profiles are integrable on the plane** (source 4565-4570). Route: the Gaussian
pointwise bound `gaussPointBound` (with `A = a`) dominates `‖hMode a‖` and `‖rMode a‖` by a
separable Gaussian `C(1+16a)² e^{-x₁²/(8a)} e^{-x₂²/(8a)}`, which is integrable on `ℝ × ℝ`
(`integrable_exp_neg_mul_sq`, `Integrable.mul_prod`); measurability is `gaussMeasurable`. -/
theorem planeIntegrable : PlaneIntegrable := by
  intro a ha
  obtain ⟨C, hC⟩ := gaussPointBound a ha
  have hC0 : 0 ≤ C := by
    have h0 := (hC a ⟨ha, le_rfl⟩ (0, 0)).1
    norm_num at h0
    linarith [norm_nonneg (hMode a (0, 0))]
  have hG : Integrable (fun x : ℝ × ℝ => C * (1 + 16 * a) ^ 2 *
      (Real.exp (-(1 / (8 * a)) * x.1 ^ 2) * Real.exp (-(1 / (8 * a)) * x.2 ^ 2))) := by
    have h1 : Integrable (fun y : ℝ => Real.exp (-(1 / (8 * a)) * y ^ 2)) :=
      integrable_exp_neg_mul_sq (by have : (0 : ℝ) < a := by linarith
                                    positivity)
    rw [Measure.volume_eq_prod]
    exact (h1.mul_prod h1).const_mul (C * (1 + 16 * a) ^ 2)
  exact ⟨Integrable.mono' hG (gaussMeasurable a).1.aestronglyMeasurable
      (ae_of_all _ fun x => pi_bound a C ha hC0 x _ (hC a ⟨ha, le_rfl⟩ x).1),
    Integrable.mono' hG (gaussMeasurable a).2.aestronglyMeasurable
      (ae_of_all _ fun x => pi_bound a C ha hC0 x _ (hC a ⟨ha, le_rfl⟩ x).2)⟩

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
