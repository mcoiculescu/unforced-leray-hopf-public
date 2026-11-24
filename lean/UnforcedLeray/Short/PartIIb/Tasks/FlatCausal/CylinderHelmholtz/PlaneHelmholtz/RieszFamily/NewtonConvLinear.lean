import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.Defs
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.NewtonKernelLocInt
import Mathlib.Analysis.Convolution

/-!
# Leaf `PartII-b:T12/1/1/2/8`: linearity of the planar Newton potential on tests

Source of record: `the November 2 reference manuscript`, line 1670 (`P_0`, the
ordinary planar cylinder projection) and lines 1923-1926 (`P_0` in the causal formula); classical
Calderón-Zygmund theory (Grafakos, *Classical Fourier Analysis*, Cor. 5.2.8).

The map `f ↦ N * f` is additive and homogeneous on planar tests: the integrand
`y ↦ N(x - y) f(y)` is integrable for a test `f` (local integrability of `N` and compact support
of `f`), so the integral splits and scalars pull out.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped ContDiff ENNReal NNReal Topology

namespace UnforcedLeray.Short.IIb.PlaneRiesz

/-- The integrand `y ↦ N(x - y) f(y)` is integrable for a planar test `f`. -/
theorem newtonConv_integrable_of_test {f : Pl → ℝ} (hf : IsTest f) (x : Pl) :
    Integrable (fun y => newtonKernel (x - y) * f y) volume := by
  obtain ⟨hs, hc⟩ := hf
  have h := (hc.convolutionExists_right (ContinuousLinearMap.lsmul ℝ ℝ)
    newtonKernelLocInt hs.continuous x).integrable
  have h2 := h.comp_sub_left x
  refine h2.congr (Eventually.of_forall fun y => ?_)
  simp [sub_sub_cancel]

/-- **Leaf `PartII-b:T12/1/1/2/8`.**  `f ↦ N * f` is additive and homogeneous on planar tests. -/
theorem newtonConvLinear : NewtonConvLinear := by
  intro f g hf hg c
  constructor
  · funext x
    simp only [newtonConv, Pi.add_apply, mul_add]
    exact integral_add (newtonConv_integrable_of_test hf x)
      (newtonConv_integrable_of_test hg x)
  · funext x
    simp only [newtonConv, Pi.smul_apply, smul_eq_mul, Pi.smul_apply]
    rw [← integral_const_mul]
    congr 1
    funext y
    ring

end UnforcedLeray.Short.IIb.PlaneRiesz
