import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.Defs
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.NewtonKernelLocInt
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.NewtonGradKernelLocInt
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.PdTest
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.NewtonKernelWeakDeriv
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.NewtonGradKernelPolar
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Leaf `PartII-b:T12/1/1/2/6`: the planar fundamental solution `∫ N Δφ = φ(0)`

Source of record: `the November 2 reference manuscript`, line 1670 (`P_0`, the
ordinary planar cylinder projection) and lines 1923-1926 (`P_0` in the causal formula); classical
Calderón-Zygmund theory (Grafakos, *Classical Fourier Analysis*, Cor. 5.2.8).

For a planar test `φ`, apply the weak derivative `NewtonKernelWeakDeriv` to the tests
`ψ_k = ∂_k φ` (tests by `PdTest`), for `k = 0, 1`:
`∫ N ∂_k∂_k φ = -∫ ∂_k N ∂_k φ`.  Adding the two identities and using the flux identity
`NewtonGradKernelPolar` (`∫ ∇N · ∇φ = -φ(0)`) gives `∫ N Δφ = φ(0)`.  The integrability needed to
split the integrals comes from local integrability of `N` and `∂_k N` against compactly supported
continuous functions.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped ContDiff ENNReal NNReal Topology

namespace UnforcedLeray.Short.IIb.PlaneRiesz

/-- **Leaf `PartII-b:T12/1/1/2/6`.**  `∫ N Δφ = φ(0)` for a planar test `φ`. -/
theorem newtonKernelLaplace : NewtonKernelLaplace := by
  intro φ hφ
  have hpd0 : IsTest (pd 0 φ) := pdTest 0 φ hφ
  have hpd1 : IsTest (pd 1 φ) := pdTest 1 φ hφ
  have hpp0 : IsTest (pd 0 (pd 0 φ)) := pdTest 0 (pd 0 φ) hpd0
  have hpp1 : IsTest (pd 1 (pd 1 φ)) := pdTest 1 (pd 1 φ) hpd1
  -- integrability of the pieces
  have I0 : Integrable (fun y => newtonKernel y * pd 0 (pd 0 φ) y) volume := by
    have := LocallyIntegrable.integrable_smul_right_of_hasCompactSupport
      (μ := volume) newtonKernelLocInt hpp0.1.continuous hpp0.2
    simpa [smul_eq_mul] using this
  have I1 : Integrable (fun y => newtonKernel y * pd 1 (pd 1 φ) y) volume := by
    have := LocallyIntegrable.integrable_smul_right_of_hasCompactSupport
      (μ := volume) newtonKernelLocInt hpp1.1.continuous hpp1.2
    simpa [smul_eq_mul] using this
  have G0 : Integrable (fun y => newtonGradKernel 0 y * pd 0 φ y) volume := by
    have := LocallyIntegrable.integrable_smul_right_of_hasCompactSupport
      (μ := volume) (newtonGradKernelLocInt 0) hpd0.1.continuous hpd0.2
    simpa [smul_eq_mul] using this
  have G1 : Integrable (fun y => newtonGradKernel 1 y * pd 1 φ y) volume := by
    have := LocallyIntegrable.integrable_smul_right_of_hasCompactSupport
      (μ := volume) (newtonGradKernelLocInt 1) hpd1.1.continuous hpd1.2
    simpa [smul_eq_mul] using this
  -- the two weak-derivative identities
  have W0 := newtonKernelWeakDeriv 0 (pd 0 φ) hpd0
  have W1 := newtonKernelWeakDeriv 1 (pd 1 φ) hpd1
  -- splitting the integrals
  have split : (∫ y, newtonKernel y * (pd 0 (pd 0 φ) y + pd 1 (pd 1 φ) y))
      = (∫ y, newtonKernel y * pd 0 (pd 0 φ) y) + (∫ y, newtonKernel y * pd 1 (pd 1 φ) y) := by
    rw [← integral_add I0 I1]
    congr 1
    funext y
    ring
  have split2 : (∫ y, (newtonGradKernel 0 y * pd 0 φ y + newtonGradKernel 1 y * pd 1 φ y))
      = (∫ y, newtonGradKernel 0 y * pd 0 φ y) + (∫ y, newtonGradKernel 1 y * pd 1 φ y) :=
    integral_add G0 G1
  -- the flux identity
  have hP := newtonGradKernelPolar φ hφ
  linarith [split, split2, W0, W1, hP]

end UnforcedLeray.Short.IIb.PlaneRiesz
