import UnforcedLeray.Units.B0284.Defs

/-!
# Age derivative of the literal planar Gaussian heat kernel

This is a calculus identity for B0284's actual kernel. At positive age it identifies the heat-age
derivative with the planar spatial Laplacian of the kernel, the kernel-level input to the actual
cylinder heat generator.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.HeatCylinder

open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.B0284 (heatKernel2)
open UnforcedLeray.B0191 (heatKernel)

/-- The explicit age derivative of the two-dimensional Gaussian kernel. -/
def heatKernel2AgeDerivative (θ : ℝ) (w : Plane) : ℝ :=
  heatKernel2 θ w * ((w.1 ^ 2 + w.2 ^ 2) / (4 * θ ^ 2) - 1 / θ)

private theorem hasDerivAt_heatKernel1_age {θ x : ℝ} (hθ : 0 < θ) :
    HasDerivAt (fun t : ℝ => heatKernel 1 t x)
      (heatKernel 1 θ x * (x ^ 2 / (4 * θ ^ 2) - 1 / (2 * θ))) θ := by
  have harg : HasDerivAt (fun t : ℝ => 4 * Real.pi * t) (4 * Real.pi) θ := by
    simpa using (hasDerivAt_id θ).const_mul (4 * Real.pi)
  have hargPos : 0 < 4 * Real.pi * θ := by positivity
  have hsqrt := (Real.hasDerivAt_sqrt (ne_of_gt hargPos)).comp θ harg
  change HasDerivAt (fun t : ℝ => Real.sqrt (4 * Real.pi * t)) _ θ at hsqrt
  have hsqrt0 : Real.sqrt (4 * Real.pi * θ) ≠ 0 := by positivity
  have hinv := hsqrt.inv hsqrt0
  have hsquares : (Real.sqrt (4 * Real.pi * θ)) ^ 2 = 4 * Real.pi * θ :=
    Real.sq_sqrt (le_of_lt hargPos)
  have hnorm : HasDerivAt (fun t : ℝ => (Real.sqrt (4 * Real.pi * t))⁻¹)
      ((Real.sqrt (4 * Real.pi * θ))⁻¹ * (-(1 / (2 * θ)))) θ := by
    convert hinv using 1
    all_goals try rfl
    rw [hsquares]
    field_simp [hsqrt0, ne_of_gt hθ] <;> ring
  have hexpArg : HasDerivAt (fun t : ℝ => -x ^ 2 / (4 * t))
      (x ^ 2 / (4 * θ ^ 2)) θ := by
    have hinv' := (hasDerivAt_id θ).inv (ne_of_gt hθ)
    convert (hinv'.const_mul (-(x ^ 2 / 4))) using 1
    all_goals try rfl
    all_goals try simp [id]
    all_goals try (funext t; simp [id])
    all_goals
      field_simp [ne_of_gt hθ] <;> ring
  have hexp := hexpArg.exp
  have hprod := hnorm.mul hexp
  have hfun : (fun t : ℝ => heatKernel 1 t x) = fun t =>
      (Real.sqrt (4 * Real.pi * t))⁻¹ * Real.exp (-x ^ 2 / (4 * t)) := by
    funext t
    simp [heatKernel]
  rw [hfun]
  convert hprod using 1
  all_goals try rfl
  all_goals try (funext t; rfl)
  all_goals
    simp only [heatKernel]
    field_simp [ne_of_gt hθ] <;> ring

/-- The derivative in heat age of B0284's actual planar Gaussian kernel. -/
theorem hasDerivAt_heatKernel2_age {θ : ℝ} (hθ : 0 < θ) (w : Plane) :
    HasDerivAt (fun τ : ℝ => heatKernel2 τ w)
      (heatKernel2AgeDerivative θ w) θ := by
  have hq := hasDerivAt_heatKernel1_age hθ (x := w.1)
  have he := hasDerivAt_heatKernel1_age hθ (x := w.2)
  have hprod := hq.mul he
  have hfun : (fun τ : ℝ => heatKernel2 τ w) = fun τ =>
      heatKernel 1 τ w.1 * heatKernel 1 τ w.2 := by
    rfl
  rw [hfun]
  unfold heatKernel2AgeDerivative UnforcedLeray.B0284.heatKernel2
  convert hprod using 1
  all_goals try rfl
  all_goals
    field_simp [ne_of_gt hθ] <;> ring

end UnforcedLeray.HeatCylinder

#print axioms UnforcedLeray.HeatCylinder.hasDerivAt_heatKernel2_age
