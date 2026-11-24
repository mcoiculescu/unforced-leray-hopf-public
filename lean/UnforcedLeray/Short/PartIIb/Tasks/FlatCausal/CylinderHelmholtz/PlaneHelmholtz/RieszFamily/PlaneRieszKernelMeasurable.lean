import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.Defs

/-!
# Measurability of the planar Riesz kernel

Source of record: `the November 2 reference manuscript`, line 1670 (`P_0`, the
ordinary planar cylinder projection) and lines 1923-1926 (`P_0` in the causal formula);
Grafakos, *Classical Fourier Analysis*, Cor. 5.2.8.

The kernel `planeRieszKernel i k` is an `if x = 0` on the closed set `{0}`, of a rational
expression in the coordinates of `x`, so it is Borel measurable.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped Topology NNReal ENNReal

namespace UnforcedLeray.Short.IIb.PlaneRiesz

/-- The planar Riesz kernels `K_{ik}` are measurable (`PlaneRieszKernelMeasurable`). -/
theorem planeRieszKernelMeasurable : PlaneRieszKernelMeasurable := by
  intro i k
  unfold planeRieszKernel
  refine Measurable.ite (measurableSet_singleton (0 : Pl)) measurable_const ?_
  generalize (if i = k then (1 : ℝ) else 0) = c
  fun_prop

end UnforcedLeray.Short.IIb.PlaneRiesz
