import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.Defs
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.PlaneHelmholtz.RieszFamily.PdTest

/-!
# Leaf `PartII-b:T12/1/1/2/13`: the divergence of a test field is a test

Source of record: `the November 2 reference manuscript`, line 1670 (`P_0`, the
ordinary planar cylinder projection) and lines 1923-1926 (`P_0` in the causal formula); classical
Calderón-Zygmund theory (Grafakos, *Classical Fourier Analysis*, Cor. 5.2.8).

For tests `F_k` (smooth with compact support) on the plane, `div F = Σ_i ∂_i F_i` is a finite sum
of partial derivatives of tests.  Each `∂_i F_i` is a test by `pdTest`, and a finite sum of
smooth compactly supported functions is smooth with compact support.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped ContDiff ENNReal NNReal Topology

namespace UnforcedLeray.Short.IIb.PlaneRiesz

/-- **Leaf `PartII-b:T12/1/1/2/13`.**  The divergence of a test field is a test. -/
theorem divTestIsTest : DivTestIsTest := by
  intro F hF
  have hpd : ∀ i : Fin 2, IsTest (pd i (F i)) := fun i => pdTest i (F i) (hF i)
  refine ⟨?_, ?_⟩
  · unfold divTest
    exact ContDiff.sum fun i _ => (hpd i).1
  · unfold divTest
    exact HasCompactSupport.finset_sum (s := Finset.univ) (f := fun i => pd i (F i))
      fun i _ => (hpd i).2

end UnforcedLeray.Short.IIb.PlaneRiesz
