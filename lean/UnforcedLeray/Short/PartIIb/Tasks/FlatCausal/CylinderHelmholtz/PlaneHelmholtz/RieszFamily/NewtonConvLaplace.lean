import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.Defs
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.PdTest
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.NewtonKernelLaplace
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.NewtonConvPd
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.NewtonConvLinear
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Support

/-!
# Leaf `PartII-b:T12/1/1/2/10`: the planar Newton potential inverts the Laplacian on tests

Source of record: `the November 2 reference manuscript`, line 1670 (`P_0`, the
ordinary planar cylinder projection) and lines 1923-1926 (`P_0` in the causal formula); classical
Calderón-Zygmund theory (Grafakos, *Classical Fourier Analysis*, Cor. 5.2.8).

For a planar test `f`, `Δ (N * f) = f`.  By `NewtonConvPd` the derivatives pass inside the
convolution, `∂_k∂_k (N * f) = N * ∂_k∂_k f`; by `NewtonConvLinear` the two summands add to
`N * (Δf)`.  The substitution `y = x + z` and the evenness of `N` turn this into
`∫ N(z) Δ(f(x + ·))(z) dz`, which is `f(x)` by `NewtonKernelLaplace` applied to the test
`φ = f(x + ·)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped ContDiff ENNReal NNReal Topology

namespace UnforcedLeray.Short.IIb.PlaneRiesz

/-- **Leaf `PartII-b:T12/1/1/2/10`.**  `Δ (N * f) = f` for a planar test `f`. -/
theorem newtonConvLaplace : NewtonConvLaplace := by
  intro f hf x
  have hd : ∀ k : Fin 2, pd k (pd k (newtonConv f)) = newtonConv (pd k (pd k f)) := by
    intro k
    rw [newtonConvPd k f hf, newtonConvPd k (pd k f) (pdTest k f hf)]
  rw [hd 0, hd 1]
  have hsum : newtonConv (pd 0 (pd 0 f) + pd 1 (pd 1 f))
      = newtonConv (pd 0 (pd 0 f)) + newtonConv (pd 1 (pd 1 f)) :=
    (newtonConvLinear (pd 0 (pd 0 f)) (pd 1 (pd 1 f))
      (pdTest 0 (pd 0 f) (pdTest 0 f hf)) (pdTest 1 (pd 1 f) (pdTest 1 f hf)) 1).1
  have hsum' : newtonConv (pd 0 (pd 0 f)) x + newtonConv (pd 1 (pd 1 f)) x
      = newtonConv (pd 0 (pd 0 f) + pd 1 (pd 1 f)) x := by
    simp only [hsum, Pi.add_apply]
  rw [hsum']
  show ∫ y, newtonKernel (x - y) * (pd 0 (pd 0 f) + pd 1 (pd 1 f)) y = f x
  simp only [Pi.add_apply]
  have hN : ∀ z : Pl, newtonKernel (x - (x + z)) = newtonKernel z := by
    intro z
    have hz : x - (x + z) = -z := by abel
    rw [hz]
    simp [newtonKernel]
  have hpt : ∀ (g : Pl → ℝ) (k : Fin 2) (z : Pl),
      pd k (fun w => g (x + w)) z = pd k g (x + z) := by
    intro g k z
    unfold pd
    rw [fderiv_comp_add_left]
  have hφ0 : pd 0 (pd 0 (fun w => f (x + w))) = fun z => pd 0 (pd 0 f) (x + z) := by
    have h1 : pd 0 (fun w => f (x + w)) = fun w => pd 0 f (x + w) := funext (hpt f 0)
    rw [h1]
    funext z
    exact hpt (pd 0 f) 0 z
  have hφ1 : pd 1 (pd 1 (fun w => f (x + w))) = fun z => pd 1 (pd 1 f) (x + z) := by
    have h1 : pd 1 (fun w => f (x + w)) = fun w => pd 1 f (x + w) := funext (hpt f 1)
    rw [h1]
    funext z
    exact hpt (pd 1 f) 1 z
  have hsub : ∫ y, newtonKernel (x - y) * (pd 0 (pd 0 f) y + pd 1 (pd 1 f) y)
      = ∫ z, newtonKernel (x - (x + z)) * (pd 0 (pd 0 f) (x + z) + pd 1 (pd 1 f) (x + z)) :=
    (integral_add_left_eq_self
      (fun y => newtonKernel (x - y) * (pd 0 (pd 0 f) y + pd 1 (pd 1 f) y)) x).symm
  rw [hsub]
  have hφT : IsTest (fun w => f (x + w)) :=
    ⟨hf.1.comp (contDiff_const.add contDiff_id),
      hf.2.comp_homeomorph (Homeomorph.addLeft x)⟩
  have hK := newtonKernelLaplace (fun w => f (x + w)) hφT
  simp only [hN]
  simpa only [hφ0, hφ1, add_zero] using hK

end UnforcedLeray.Short.IIb.PlaneRiesz
