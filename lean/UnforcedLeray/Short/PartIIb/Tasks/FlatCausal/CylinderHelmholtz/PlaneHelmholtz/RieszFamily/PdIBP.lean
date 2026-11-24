import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.Defs

/-!
# Integration by parts on the plane for a test function against a smooth function

Source of record: `the November 2 reference manuscript`, line 1670 (the planar
projection `P_0 = I - ∇Δ⁻¹ div`) and lines 1923-1926 (`P_0` in the causal formula); classical
Calderón-Zygmund theory, Grafakos, *Classical Fourier Analysis*, Cor. 5.2.8.

For a smooth `u` and a test function `f` (smooth with compact support) on `ℝ²`,
`∫ (∂_k f) u = -∫ f (∂_k u)`.  The proof is the Mathlib integration by parts for a
Fréchet derivative in a fixed direction, with the three integrability side conditions
coming from continuity and compact support of `f`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped ContDiff Topology

namespace UnforcedLeray.Short.IIb.PlaneRiesz

/-- **Leaf `PartII-b:T12/1/1/2/36`.** Integration by parts of a test function against a smooth
function in the coordinate direction `k`. -/
theorem pdIBP : PdIBP := by
  intro k u f hu hf
  obtain ⟨hfC, hfS⟩ := hf
  have huD : Differentiable ℝ u := hu.differentiable (by simp)
  have hfD : Differentiable ℝ f := hfC.differentiable (by simp)
  have huC : Continuous u := hu.continuous
  have hfC' : Continuous f := hfC.continuous
  have hdu : Continuous (fderiv ℝ u) := hu.continuous_fderiv (by simp)
  have hdf : Continuous (fderiv ℝ f) := hfC.continuous_fderiv (by simp)
  have hcont1 : Continuous (fun x => fderiv ℝ u x (Pi.single k (1 : ℝ))) :=
    hdu.clm_apply continuous_const
  have hcont2 : Continuous (fun x => fderiv ℝ f x (Pi.single k (1 : ℝ))) :=
    hdf.clm_apply continuous_const
  have I1 : Integrable (fun x => fderiv ℝ u x (Pi.single k (1 : ℝ)) * f x) :=
    Continuous.integrable_of_hasCompactSupport (hcont1.mul hfC')
      (hfS.mul_left (f := fun x => fderiv ℝ u x (Pi.single k (1 : ℝ))))
  have I2 : Integrable (fun x => u x * fderiv ℝ f x (Pi.single k (1 : ℝ))) :=
    Continuous.integrable_of_hasCompactSupport (huC.mul hcont2)
      (((hfS.fderiv_apply (𝕜 := ℝ) (Pi.single k (1 : ℝ))).mul_left (f := u)))
  have I3 : Integrable (fun x => u x * f x) :=
    Continuous.integrable_of_hasCompactSupport (huC.mul hfC') (hfS.mul_left (f := u))
  have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume) (f := u) (g := f)
    (v := Pi.single k (1 : ℝ)) I1 I2 I3 (fun x _ => huD x) (fun x _ => hfD x)
  have h1 : ∫ x, pd k f x * u x = ∫ x, u x * fderiv ℝ f x (Pi.single k (1 : ℝ)) := by
    congr 1
    funext x
    simp only [pd]
    ring
  have h2 : ∫ x, f x * pd k u x = ∫ x, fderiv ℝ u x (Pi.single k (1 : ℝ)) * f x := by
    congr 1
    funext x
    simp only [pd]
    ring
  rw [h1, h2]
  exact key

end UnforcedLeray.Short.IIb.PlaneRiesz
