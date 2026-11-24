import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.Defs
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.NewtonConvContDiff

/-!
# Leaf `PartII-b:T12/1/1/2/16`: the test-level Riesz pairs are `C^∞`

Source of record: `the November 2 reference manuscript`, line 1670 (`P_0`, the
ordinary planar cylinder projection) and lines 1923-1926 (`P_0` in the causal formula); classical
Calderón-Zygmund theory (Grafakos, *Classical Fourier Analysis*, Cor. 5.2.8).

`S_{ik} f = ∂_i ∂_k (N * f)`.  The Newton potential `N * f` is `C^∞` for a test `f`
(`NewtonConvContDiff`), and a partial derivative of a `C^∞` function is `C^∞`
(`ContDiff.fderiv_right` and `ContDiff.clm_apply`), so `S_{ik} f` is `C^∞`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped ContDiff ENNReal NNReal Topology

namespace UnforcedLeray.Short.IIb.PlaneRiesz

/-- A partial derivative of a `C^∞` function on the plane is `C^∞`. -/
theorem rieszPd_contDiff {g : Pl → ℝ} (hg : ContDiff ℝ ∞ g) (k : Fin 2) :
    ContDiff ℝ ∞ (pd k g) := by
  have hfd : ContDiff ℝ ∞ (fderiv ℝ g) := hg.fderiv_right (by simp)
  exact hfd.clm_apply contDiff_const

/-- **Leaf `PartII-b:T12/1/1/2/16`.**  `S_{ik} f` is `C^∞` for a planar test `f`. -/
theorem rieszTestContDiff : RieszTestContDiff := by
  intro i k f hf
  unfold rieszTest
  exact rieszPd_contDiff (rieszPd_contDiff (newtonConvContDiff f hf) k) i

end UnforcedLeray.Short.IIb.PlaneRiesz
