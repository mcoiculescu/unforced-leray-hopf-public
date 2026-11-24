import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.Defs
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.NewtonKernelLocInt
import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-!
# Leaf `PartII-b:T12/1/1/2/7`: smoothness of the planar Newton potential of a test

Source of record: `the November 2 reference manuscript`, line 1670 (`P_0`, the
ordinary planar cylinder projection) and lines 1923-1926 (`P_0` in the causal formula); classical
Calderón-Zygmund theory (Grafakos, *Classical Fourier Analysis*, Cor. 5.2.8).

For a planar test `f` (smooth, compactly supported), `N * f` is a convolution of the locally
integrable planar Newton kernel `N` with a compactly supported smooth function, hence `C^∞`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped ContDiff ENNReal NNReal Topology

namespace UnforcedLeray.Short.IIb.PlaneRiesz

/-- **Leaf `PartII-b:T12/1/1/2/7`.**  `N * f` is `C^∞` for a planar test `f`. -/
theorem newtonConvContDiff : NewtonConvContDiff := by
  intro f hf
  obtain ⟨hs, hc⟩ := hf
  have hconv : newtonConv f =
      convolution newtonKernel f (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
    funext x
    rw [convolution_def, newtonConv,
      ← integral_sub_left_eq_self (fun y => newtonKernel (x - y) * f y) volume x]
    simp [sub_sub_cancel]
  rw [hconv]
  exact hc.contDiff_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ)
    newtonKernelLocInt hs

end UnforcedLeray.Short.IIb.PlaneRiesz
