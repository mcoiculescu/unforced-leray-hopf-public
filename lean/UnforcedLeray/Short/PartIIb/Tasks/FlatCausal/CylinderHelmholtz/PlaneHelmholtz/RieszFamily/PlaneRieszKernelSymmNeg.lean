import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.Defs

/-!
# Symmetry of the planar Riesz kernel under `z ↦ -z`

Source of record: `the November 2 reference manuscript`, line 1670 (`P_0`, the
ordinary planar cylinder projection) and lines 1923-1926 (`P_0` in the causal formula);
Grafakos, *Classical Fourier Analysis*, Cor. 5.2.8.

The kernel `planeRieszKernel i k` is even in the sense `K_{ki}(-z) = K_{ik}(z)`: the diagonal
term is unchanged, the squares are unchanged, and the cross term `x_i x_k` is a product of two
negated coordinates, hence unchanged.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped Topology NNReal ENNReal

namespace UnforcedLeray.Short.IIb.PlaneRiesz

/-- `K_{ki}(-z) = K_{ik}(z)` (planar Riesz kernel, `PlaneRieszKernelSymmNeg`). -/
theorem planeRieszKernelSymmNeg : PlaneRieszKernelSymmNeg := by
  intro i k z
  by_cases hz : z = 0
  · subst hz
    simp [planeRieszKernel]
  · have hz' : -z ≠ 0 := neg_ne_zero.mpr hz
    unfold planeRieszKernel
    rw [if_neg hz', if_neg hz]
    have hsq : ((-z) 0 ^ 2 + (-z) 1 ^ 2) = z 0 ^ 2 + z 1 ^ 2 := by simp
    have hc : (if k = i then (1 : ℝ) else 0) = (if i = k then (1 : ℝ) else 0) := by
      by_cases h : i = k
      · subst h
        rfl
      · have h' : k ≠ i := fun h'' => h h''.symm
        rw [if_neg h, if_neg h']
    rw [hsq, hc]
    simp only [Pi.neg_apply]
    ring

end UnforcedLeray.Short.IIb.PlaneRiesz
