import UnforcedLeray.Short.PartIIa.Sub.F05
import UnforcedLeray.Short.PartIIa.Tasks.F05aAdjResolventSolution
import UnforcedLeray.Short.PartIIa.Tasks.F05bSliceContOfDecay

/-!
# Part II-a, task `PartII-a:F05`: homogeneous uniqueness (final assembly)

Source of record: `the November 2 reference manuscript`, lines 1403-1423.
The target is obtained by applying the conditional theorem `bodyOp_uniqueness_of`
(`Sub/F05.lean`) to the adjoint-resolvent input `adjointResolventSchwartz_of`, which is fed by the
two leaves `adjResolventSolution` (`Tasks/F05aAdjResolventSolution.lean`, task `PartII-a:F05/1`)
and `sliceContOfDecay` (`Tasks/F05bSliceContOfDecay.lean`, task `PartII-a:F05/2`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp

/-- Task `PartII-a:F05`: a distributional solution `w` of the homogeneous body equation
`(μ + L₀) w = 0` in `Y_r`, `1 < r < 3`, `Re μ + γ_r > 0`, vanishes. -/
theorem bodyOp_uniqueness (r : ℝ≥0∞) [Fact (1 ≤ r)] (h1 : 1 < r) (h3 : r < 3) (P : ℝ)
    [Fact (0 < P)] (nu : ℝ) (hnu : 0 < nu) (mu : ℂ) (hmu : 0 < mu.re + gammaR r) (w : Yq P r)
    (hw : HasPhaseOp (fun Phi => mu • Phi + L0T nu Phi) w 0) : w = 0 :=
  bodyOp_uniqueness_of (adjointResolventSchwartz_of adjResolventSolution sliceContOfDecay) r h1 h3
    P nu hnu mu hmu w hw

end UnforcedLeray.Short.PartIIa
