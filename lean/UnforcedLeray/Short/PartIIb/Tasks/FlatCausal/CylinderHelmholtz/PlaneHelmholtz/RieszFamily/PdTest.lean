import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.Defs

/-!
# Leaf `PartII-b:T12/1/1/2/1`: a partial derivative of a test is a test

Source of record: `the November 2 reference manuscript`, line 1670 (`P_0`, the
ordinary planar cylinder projection) and lines 1923-1926 (`P_0` in the causal formula); classical
Calderón-Zygmund theory (Grafakos, *Classical Fourier Analysis*, Cor. 5.2.8).

For a test `f` (smooth with compact support) on the plane, `∂_k f` is again smooth with compact
support: it is the derivative of `f` in the direction `e_k`, so smoothness comes from
`fderiv` of a `C^∞` map and the support from `HasCompactSupport.fderiv_apply`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped ContDiff ENNReal NNReal Topology

namespace UnforcedLeray.Short.IIb.PlaneRiesz

/-- **Leaf `PartII-b:T12/1/1/2/1`.**  `∂_k` maps tests to tests. -/
theorem pdTest : PdTest := by
  intro k f hf
  obtain ⟨hsmooth, hsupp⟩ := hf
  refine ⟨?_, ?_⟩
  · unfold pd
    have hfd : ContDiff ℝ ∞ (fderiv ℝ f) := hsmooth.fderiv_right (by simp)
    exact hfd.clm_apply contDiff_const
  · unfold pd
    exact hsupp.fderiv_apply ℝ (Pi.single k 1)

end UnforcedLeray.Short.IIb.PlaneRiesz
