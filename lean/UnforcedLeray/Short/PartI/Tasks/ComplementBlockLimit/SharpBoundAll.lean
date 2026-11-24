import UnforcedLeray.Short.PartI.Sub.C03
import UnforcedLeray.Short.PartI.Tasks.FreeDiffusionEvolution
import UnforcedLeray.Short.PartI.Tasks.FreeDiffusionEvolution.Stability

/-!
# Target `PartI:C03/1`: `freeSharpBoundAll`

Source of record: `the November 2 reference manuscript`, lines 1024-1028
(the sharp bound `‖F_β(t,s)‖ ≤ exp{-γ(t-s) + |Re κ| β_* (t-s)}` for every free evolution with
measurable `0 ≤ β ≤ β_*`).

Method. On a block `[s,t]` every free evolution is the Dyson sum of the same family and the same
bounded interaction (`fds_hasSum`). Given a free evolution `F`, take the free evolution `F'`
produced by `exists_freeDiffusionEvolution`. The two Dyson sums have identical terms, so
`F t s = F' t s` by uniqueness of limits, and the sharp bound of `F'` transfers to `F`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray

/-- **Target `PartI:C03/1`** (source lines 1024-1028): every free evolution `F` of
`IsFreeDiffusionEvolution` with measurable `0 ≤ β ≤ β_*` satisfies the sharp norm bound
`‖F(t,s)‖ ≤ exp(-Re λ (t-s) + |Re κ| β_* (t-s))` for `s ≤ t`. -/
theorem freeSharpBoundAll : FreeSharpBoundAll := by
  intro lam kappa βs β hβm hβb F hF s t hst
  obtain ⟨F', hF', hbd⟩ := exists_freeDiffusionEvolution lam kappa βs hβm hβb
  have heq : F t s = F' t s := by
    refine ContinuousLinearMap.ext fun x => ?_
    exact (fds_hasSum lam kappa s t βs β hβm hβb F hF t hst le_rfl x).unique
      (fds_hasSum lam kappa s t βs β hβm hβb F' hF' t hst le_rfl x)
  rw [heq]
  exact hbd s t hst

end UnforcedLeray.Short.PartI
