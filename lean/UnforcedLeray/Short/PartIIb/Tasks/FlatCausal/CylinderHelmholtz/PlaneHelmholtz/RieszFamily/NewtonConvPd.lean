import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.Defs
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.PdTest
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.NewtonKernelLocInt
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.NewtonConvContDiff
import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-!
# Leaf `PartII-b:T12/1/1/2/9`: the planar Newton potential commutes with `∂_k`

Source of record: `the November 2 reference manuscript`, line 1670 (`P_0`, the
ordinary planar cylinder projection) and lines 1923-1926 (`P_0` in the causal formula); classical
Calderón-Zygmund theory (Grafakos, *Classical Fourier Analysis*, Cor. 5.2.8).

For a planar test `f`, `∂_k (N * f) = N * ∂_k f`: the convolution derivative of
`HasCompactSupport.hasFDerivAt_convolution_right` is the convolution with the derivative of `f`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped ContDiff ENNReal NNReal Topology

namespace UnforcedLeray.Short.IIb.PlaneRiesz

/-- **Leaf `PartII-b:T12/1/1/2/9`.**  `∂_k (N * f) = N * ∂_k f` for a planar test `f`. -/
theorem newtonConvPd : NewtonConvPd := by
  intro k f hf
  obtain ⟨hs, hc⟩ := hf
  have hconv : ∀ g : Pl → ℝ,
      newtonConv g = convolution newtonKernel g (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
    intro g
    funext x
    rw [convolution_def, newtonConv,
      ← integral_sub_left_eq_self (fun y => newtonKernel (x - y) * g y) volume x]
    simp [sub_sub_cancel]
  have hC1 : ContDiff ℝ 1 f := hs.of_le (by exact_mod_cast le_top)
  funext x
  have hd := hc.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ)
    newtonKernelLocInt hC1 x
  show fderiv ℝ (newtonConv f) x (Pi.single k 1) = newtonConv (pd k f) x
  rw [hconv f, hd.fderiv]
  rw [convolution_precompR_apply (ContinuousLinearMap.lsmul ℝ ℝ) newtonKernelLocInt
    (hc.fderiv ℝ) (hs.continuous_fderiv (by simp)) x (Pi.single k 1)]
  rw [hconv (pd k f)]
  rfl

end UnforcedLeray.Short.IIb.PlaneRiesz
