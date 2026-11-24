import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.Defs
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.PdTest
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.NewtonConvPd

/-!
# Leaf `PartII-b:T12/1/1/2/14`: the Riesz pair is `∂_i (N * ∂_k f)` on tests

Source of record: `the November 2 reference manuscript`, line 1670 (`P_0`, the
ordinary planar cylinder projection) and lines 1923-1926 (`P_0` in the causal formula); classical
Calderón-Zygmund theory (Grafakos, *Classical Fourier Analysis*, Cor. 5.2.8).

Since `S_{ik} f = ∂_i ∂_k (N * f)` and `∂_k (N * f) = N * ∂_k f` for a test `f`, the test-level
Riesz pair equals `∂_i (N * ∂_k f)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped ContDiff ENNReal NNReal Topology

namespace UnforcedLeray.Short.IIb.PlaneRiesz

/-- **Leaf `PartII-b:T12/1/1/2/14`.**  `S_{ik} f = ∂_i (N * ∂_k f)` for a planar test `f`. -/
theorem rieszTestEqConvPd : RieszTestEqConvPd := by
  intro i k f hf
  unfold rieszTest
  rw [newtonConvPd k f hf]

end UnforcedLeray.Short.IIb.PlaneRiesz
