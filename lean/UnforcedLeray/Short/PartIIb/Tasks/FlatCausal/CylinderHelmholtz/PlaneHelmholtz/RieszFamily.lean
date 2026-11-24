import UnforcedLeray.Short.PartIIb.Sub.T12_1_1
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.Defs
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.RieszL2Exists
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.RieszL2Transpose
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.RieszL2Contraction
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.RieszL2Grad
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.RieszL2Sol
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.RieszL2OffSupport
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszKernel

/-!
# The planar Riesz family exists (`PartII-b:T12/1/1/2`)

Assembly of the leaves of the planar Riesz family `S_{ik} = ∂_i ∂_k Δ⁻¹` on `L²(ℝ²)`:
the `L²` extensions `T i k` of the test-level pairs come from `rieszL2Exists`; the Calderón–Zygmund
fields (measurability, size, Hörmander condition, off-support representation) come from
`planeRieszKernelCZ` and `rieszL2OffSupport`; transposition, contraction and the two test
identities come from `rieszL2Transpose`, `rieszL2Contraction`, `rieszL2Grad`, `rieszL2Sol`.

Source of record: `the November 2 reference manuscript`, line 1670 (the planar
projection `P_0 = I - grad Δ⁻¹ div`) and lines 1923–1926; classical Calderón–Zygmund theory,
Grafakos, *Classical Fourier Analysis*, Cor. 5.2.8.

This file contains no `sorry`, no axiom and no `native_decide`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped ContDiff ENNReal NNReal Topology

namespace UnforcedLeray.Short.IIb

open PlaneRiesz

/-- **Leaf `PartII-b:T12/1/1/2`.** There is a planar Riesz family `S_{ik}` (an `L²` family of
Calderón–Zygmund convolution operators with kernels `planeRieszKernel i k`, transposing to
`S_{ki}`, with `I - S` a contraction on pairs and the two test identities). The proof chooses the
`L²` extensions `T i k` of `rieszL2Exists` and takes the constant `B` of `planeRieszKernelCZ`. -/
theorem planeRieszFamilyExists : PlaneRieszFamilyExists := by
  have hL : ∀ i k : Fin 2, ∃ T : PlaneL2 →L[ℝ] PlaneL2, ‖T‖ ≤ 1 ∧ ExtendsRieszTest T i k :=
    rieszL2Exists
  choose T _hn hT using hL
  have hK : PlaneRieszKernelCZ := planeRieszKernelCZ
  obtain ⟨B, hB⟩ := hK
  refine ⟨T, B, ?_⟩
  unfold IsPlaneRieszFamily
  refine ⟨fun i k => ?_, rieszL2Transpose T hT, rieszL2Contraction T hT,
    rieszL2Grad T hT, rieszL2Sol T hT⟩
  obtain ⟨hm, hs, hh⟩ := hB i k
  exact ⟨hm, hs, hh, rieszL2OffSupport T hT i k⟩

end UnforcedLeray.Short.IIb

end
