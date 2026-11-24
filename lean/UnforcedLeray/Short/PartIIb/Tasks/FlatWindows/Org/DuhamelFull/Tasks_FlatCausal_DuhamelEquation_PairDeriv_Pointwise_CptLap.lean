import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.DuhamelFull.Defs
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.DuhamelEquation.PairDeriv.Pointwise.CptLap
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.DuhamelFull.Sub_PartIIb_T12_7_5_1

/-!
# Part II-b, task `PartII-b:T12/7/5/1/2` (`dfe_DeqpdCptLap`): chain rule for the planar Laplacian

Source of record: `the November 2 reference manuscript`, lines 1923-1927.
For a smooth `Φ` on `Coord = ℝ × (ℝ × ℝ)`, the slice `y ↦ Φ(s, y)` has planar Laplacian
`(cpd 1 ∘ cpd 1 + cpd 2 ∘ cpd 2) Φ (s, y)`, since `fderiv` of `y ↦ Φ(s, y)` in direction `v` is
`fderiv Φ (s, y) (0, v)` and `cdir 1 = (0, (1, 0))`, `cdir 2 = (0, (0, 1))`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- **Task `PartII-b:T12/7/5/1/2`**: the planar Laplacian of `y ↦ Ψ_i(s, y)` is
`(cpd 1 ∘ cpd 1 + cpd 2 ∘ cpd 2) Ψ_i (s, y)` (SP 1923-1927). -/
theorem dfe_deqpdCptLap : UnforcedLeray.Short.IIb.dfe_DeqpdCptLap := by
  intro Ψ hΨ i s y
  exact deqpc_slice_lap (fun z => Ψ z i) (hΨ.smooth i).smooth s y

end UnforcedLeray.Short.IIb
