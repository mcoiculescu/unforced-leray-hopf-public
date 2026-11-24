import UnforcedLeray.Lib.HeatCylinder.HeatKernelAgeIntegrable

/-!
# Local age-majorants for the actual planar Gaussian

This leaf provides the positive-time locally uniform Gaussian envelope needed by dominated
parameter-integral differentiation.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.B0191 (heatKernel)
open UnforcedLeray.B0284 (heatKernel2)

/-- Explicit radial formula for the actual planar product Gaussian. -/
theorem heatKernel2_eq_radial {θ : ℝ} (hθ : 0 < θ) (w : Plane) :
    heatKernel2 θ w = (4 * Real.pi * θ)⁻¹ *
      Real.exp (-((w.1 ^ 2 + w.2 ^ 2) / (4 * θ))) := by
  unfold heatKernel2 heatKernel
  simp only [mul_one]
  have hs : Real.sqrt (4 * Real.pi * θ) ≠ 0 := by positivity
  have hsq : Real.sqrt (4 * Real.pi * θ) ^ 2 = 4 * Real.pi * θ :=
    Real.sq_sqrt (by positivity)
  calc
    (Real.sqrt (4 * Real.pi * θ))⁻¹ * Real.exp (-w.1 ^ 2 / (4 * θ)) *
        ((Real.sqrt (4 * Real.pi * θ))⁻¹ * Real.exp (-w.2 ^ 2 / (4 * θ))) =
      ((Real.sqrt (4 * Real.pi * θ))⁻¹ * (Real.sqrt (4 * Real.pi * θ))⁻¹) *
        (Real.exp (-w.1 ^ 2 / (4 * θ)) * Real.exp (-w.2 ^ 2 / (4 * θ))) := by ring
    _ = (4 * Real.pi * θ)⁻¹ * Real.exp (-((w.1 ^ 2 + w.2 ^ 2) / (4 * θ))) := by
      rw [← mul_inv, ← pow_two, hsq, ← Real.exp_add]
      congr 1
      field_simp [ne_of_gt hθ]
      ring


/-- A planar Gaussian times the coordinate-square polynomial remains integrable. -/
theorem integrable_one_add_sq_mul_heatKernel2 {θ : ℝ} (hθ : 0 < θ) :
    Integrable (fun w : Plane => (1 + w.1 ^ 2 + w.2 ^ 2) * heatKernel2 θ w) := by
  have h0 : Integrable (heatKernel 1 θ) := UnforcedLeray.B0296.integrable_heatKernel1 hθ
  have h2 : Integrable (fun x : ℝ => x ^ 2 * heatKernel 1 θ x) :=
    integrable_sq_mul_heatKernel1 hθ
  have h00 := h0.mul_prod h0
  have h20 := h2.mul_prod h0
  have h02 := h0.mul_prod h2
  have hsum : Integrable
      ((fun w : Plane => heatKernel 1 θ w.1 * heatKernel 1 θ w.2) +
       (fun w => (w.1 ^ 2 * heatKernel 1 θ w.1) * heatKernel 1 θ w.2) +
       (fun w => heatKernel 1 θ w.1 * (w.2 ^ 2 * heatKernel 1 θ w.2)))
      (volume.prod volume) := (h00.add h20).add h02
  have hEq : (fun w : Plane => (1 + w.1 ^ 2 + w.2 ^ 2) * heatKernel2 θ w) =
      (fun w => heatKernel 1 θ w.1 * heatKernel 1 θ w.2) +
       (fun w => (w.1 ^ 2 * heatKernel 1 θ w.1) * heatKernel 1 θ w.2) +
       (fun w => heatKernel 1 θ w.1 * (w.2 ^ 2 * heatKernel 1 θ w.2)) := by
    funext w
    simp [heatKernel2]
    ring
  rw [hEq, Measure.volume_eq_prod]
  exact hsum



/-- Uniform local bound for the age derivative by an integrable quadratic multiple of a wider
Gaussian. Here the wider kernel has age `2*θ₀`, while the differentiated age ranges in
`(θ₀/2, 2*θ₀)`. -/
theorem abs_heatKernel2AgeDerivative_le_local {θ₀ s : ℝ} (hθ₀ : 0 < θ₀)
    (hlo : θ₀ / 2 < s) (hhi : s < 2 * θ₀) (w : Plane) :
    |heatKernel2AgeDerivative s w| ≤
      (4 * (θ₀⁻¹ ^ 2 + 2 / θ₀)) *
        ((1 + w.1 ^ 2 + w.2 ^ 2) * heatKernel2 (2 * θ₀) w) := by
  have hs : 0 < s := lt_trans (by positivity) hlo
  have hr2 : 0 ≤ w.1 ^ 2 + w.2 ^ 2 := by positivity
  have hden₁ : θ₀ ^ 2 ≤ 4 * s ^ 2 := by nlinarith [sq_nonneg (2 * s - θ₀)]
  have hden₂ : 4 * s ≤ 8 * θ₀ := by linarith
  have hcoef₁ : (w.1 ^ 2 + w.2 ^ 2) / (4 * s ^ 2) ≤
      (w.1 ^ 2 + w.2 ^ 2) / θ₀ ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    exact mul_le_mul_of_nonneg_left hden₁ hr2
  have hcoef₂ : 1 / s ≤ 2 / θ₀ := by
    rw [div_le_div_iff₀ hs hθ₀]
    nlinarith [hlo]
  have hcoeff : |(w.1 ^ 2 + w.2 ^ 2) / (4 * s ^ 2) - 1 / s| ≤
      (w.1 ^ 2 + w.2 ^ 2) / θ₀ ^ 2 + 2 / θ₀ := by
    rw [abs_le]
    have ha : 0 ≤ (w.1 ^ 2 + w.2 ^ 2) / (4 * s ^ 2) := by positivity
    have hb : 0 ≤ 1 / s := by positivity
    constructor <;> nlinarith
  have hA₀ : 0 ≤ θ₀⁻¹ ^ 2 + 2 / θ₀ := by positivity
  have hA₁ : θ₀⁻¹ ^ 2 ≤ θ₀⁻¹ ^ 2 + 2 / θ₀ := by
    exact le_add_of_nonneg_right (by positivity)
  have hA₂ : 2 / θ₀ ≤ θ₀⁻¹ ^ 2 + 2 / θ₀ := by
    exact le_add_of_nonneg_left (by positivity)
  have hcoeff' : (w.1 ^ 2 + w.2 ^ 2) / θ₀ ^ 2 + 2 / θ₀ ≤
      (θ₀⁻¹ ^ 2 + 2 / θ₀) * (1 + w.1 ^ 2 + w.2 ^ 2) := by
    have hinv : (θ₀ ^ 2)⁻¹ = θ₀⁻¹ ^ 2 := by
      field_simp [ne_of_gt hθ₀]
    rw [div_eq_mul_inv, hinv]
    calc
      (w.1 ^ 2 + w.2 ^ 2) * θ₀⁻¹ ^ 2 + 2 / θ₀ =
          θ₀⁻¹ ^ 2 * (w.1 ^ 2 + w.2 ^ 2) + 2 / θ₀ := by ring
      _ ≤ (θ₀⁻¹ ^ 2 + 2 / θ₀) * (w.1 ^ 2 + w.2 ^ 2) +
            (θ₀⁻¹ ^ 2 + 2 / θ₀) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_right hA₁ hr2) hA₂
      _ = (θ₀⁻¹ ^ 2 + 2 / θ₀) * (1 + w.1 ^ 2 + w.2 ^ 2) := by ring
  have hdiv : (w.1 ^ 2 + w.2 ^ 2) / (8 * θ₀) ≤
      (w.1 ^ 2 + w.2 ^ 2) / (4 * s) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    exact mul_le_mul_of_nonneg_left hden₂ hr2
  have hexp : Real.exp (-((w.1 ^ 2 + w.2 ^ 2) / (4 * s))) ≤
      Real.exp (-((w.1 ^ 2 + w.2 ^ 2) / (8 * θ₀))) := by
    apply Real.exp_le_exp.mpr
    exact neg_le_neg hdiv
  have hpref : (4 * Real.pi * s)⁻¹ ≤ 4 * (4 * Real.pi * (2 * θ₀))⁻¹ := by
    have hden : 2 * Real.pi * θ₀ ≤ 4 * Real.pi * s := by
      nlinarith [Real.pi_pos]
    have hrewrite : 4 * (4 * Real.pi * (2 * θ₀))⁻¹ = (2 * Real.pi * θ₀)⁻¹ := by
      field_simp <;> ring
    rw [hrewrite]
    simpa only [one_div] using one_div_le_one_div_of_le (by positivity) hden
  rw [heatKernel2AgeDerivative, heatKernel2_eq_radial hs w,
    abs_mul, abs_of_pos (by positivity)]
  have hkernel : (4 * Real.pi * s)⁻¹ *
      Real.exp (-((w.1 ^ 2 + w.2 ^ 2) / (4 * s))) ≤
      4 * ((4 * Real.pi * (2 * θ₀))⁻¹ *
        Real.exp (-((w.1 ^ 2 + w.2 ^ 2) / (8 * θ₀)))) := by
    calc
      (4 * Real.pi * s)⁻¹ * Real.exp (-((w.1 ^ 2 + w.2 ^ 2) / (4 * s))) ≤
          (4 * (4 * Real.pi * (2 * θ₀))⁻¹) *
            Real.exp (-((w.1 ^ 2 + w.2 ^ 2) / (4 * s))) :=
        mul_le_mul_of_nonneg_right hpref (Real.exp_pos _).le
      _ ≤ (4 * (4 * Real.pi * (2 * θ₀))⁻¹) *
            Real.exp (-((w.1 ^ 2 + w.2 ^ 2) / (8 * θ₀))) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = 4 * ((4 * Real.pi * (2 * θ₀))⁻¹ *
            Real.exp (-((w.1 ^ 2 + w.2 ^ 2) / (8 * θ₀)))) := by ring
  calc
    (4 * Real.pi * s)⁻¹ * Real.exp (-((w.1 ^ 2 + w.2 ^ 2) / (4 * s))) *
        |(w.1 ^ 2 + w.2 ^ 2) / (4 * s ^ 2) - 1 / s| ≤
      (4 * ((4 * Real.pi * (2 * θ₀))⁻¹ *
        Real.exp (-((w.1 ^ 2 + w.2 ^ 2) / (8 * θ₀))))) *
        ((θ₀⁻¹ ^ 2 + 2 / θ₀) * (1 + w.1 ^ 2 + w.2 ^ 2)) := by
          calc
      _ ≤ (4 * ((4 * Real.pi * (2 * θ₀))⁻¹ *
          Real.exp (-((w.1 ^ 2 + w.2 ^ 2) / (8 * θ₀))))) *
          ((w.1 ^ 2 + w.2 ^ 2) / θ₀ ^ 2 + 2 / θ₀) :=
        mul_le_mul hkernel hcoeff (abs_nonneg _) (by positivity)
      _ ≤ (4 * ((4 * Real.pi * (2 * θ₀))⁻¹ *
          Real.exp (-((w.1 ^ 2 + w.2 ^ 2) / (8 * θ₀))))) *
          ((θ₀⁻¹ ^ 2 + 2 / θ₀) * (1 + w.1 ^ 2 + w.2 ^ 2)) :=
        mul_le_mul_of_nonneg_left hcoeff' (by positivity)
    _ = (4 * (θ₀⁻¹ ^ 2 + 2 / θ₀)) *
        ((1 + w.1 ^ 2 + w.2 ^ 2) *
          ((4 * Real.pi * (2 * θ₀))⁻¹ *
            Real.exp (-((w.1 ^ 2 + w.2 ^ 2) / (8 * θ₀))))) := by ring
    _ = (4 * (θ₀⁻¹ ^ 2 + 2 / θ₀)) *
        ((1 + w.1 ^ 2 + w.2 ^ 2) * heatKernel2 (2 * θ₀) w) := by
          rw [heatKernel2_eq_radial (by positivity) w]
          rw [show 4 * (2 * θ₀) = 8 * θ₀ by ring]

end UnforcedLeray.HeatCylinder

#print axioms UnforcedLeray.HeatCylinder.heatKernel2_eq_radial
#print axioms UnforcedLeray.HeatCylinder.integrable_one_add_sq_mul_heatKernel2
#print axioms UnforcedLeray.HeatCylinder.abs_heatKernel2AgeDerivative_le_local
