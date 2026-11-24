import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T09_5
import UnforcedLeray.Short.PartIIb.Tasks.DriftNvC.Smooth.SmoothPt.NicePhaseTest

/-!
# Part II-b, task `PartII-b:T09/5/6`: the lift of a nice profile is `C²`, periodic, compactly supported

Source: `the November 2 reference manuscript` lines 1639-1668, 1912-1916.
Reuses `nvCNicePhaseTest_proof` (`T08/1/2/1`): `N_v b` is a phase test (smooth, periodic,
vanishing for large `‖y‖`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff ENNReal

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411
  UnforcedLeray.B0412

theorem lapNvCSmooth_proof : UnforcedLeray.Short.IIb.LapNvCSmooth := by
  intro c ε b hc hε hb
  obtain ⟨hs, hp, R, hR⟩ := nvCNicePhaseTest_proof c ε b hc hε hb
  refine ⟨hs.of_le (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤)), hp, Metric.closedBall 0 R,
    isCompact_closedBall _ _, ?_⟩
  intro t y hy
  apply hR
  simpa [mem_closedBall_zero_iff, not_le] using hy

end UnforcedLeray.Short.IIb

#print axioms UnforcedLeray.Short.IIb.lapNvCSmooth_proof
