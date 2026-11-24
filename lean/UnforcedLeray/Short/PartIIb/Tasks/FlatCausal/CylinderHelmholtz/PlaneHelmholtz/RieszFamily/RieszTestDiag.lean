import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.Defs
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.NewtonConvLaplace

/-!
# Leaf `PartII-b:T12/1/1/2/33`: the diagonal sum of the planar Riesz tests is the identity

Source of record: `the November 2 reference manuscript`, line 1670 (`P_0`, the
ordinary planar cylinder projection) and lines 1923-1926 (`P_0` in the causal formula); classical
Calderón-Zygmund theory (Grafakos, *Classical Fourier Analysis*, Cor. 5.2.8).

For a planar test `f`, `S_{ik} f = ∂_i ∂_k (N * f)`, so `S_{00} f + S_{11} f = Δ (N * f)`, which is
`f` by `NewtonConvLaplace`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped ContDiff ENNReal NNReal Topology

namespace UnforcedLeray.Short.IIb.PlaneRiesz

/-- **Leaf `PartII-b:T12/1/1/2/33`.**  `Σ_k S_{kk} f = f` for a planar test `f`. -/
theorem rieszTestDiag : RieszTestDiag := by
  intro f hf x
  exact newtonConvLaplace f hf x

end UnforcedLeray.Short.IIb.PlaneRiesz
