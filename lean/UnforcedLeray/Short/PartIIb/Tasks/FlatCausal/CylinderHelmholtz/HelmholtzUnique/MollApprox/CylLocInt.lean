import UnforcedLeray.Short.PartIIb.Sub.T12_1_3_1
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.CylinderHelmholtz.HelmholtzUnique.MollApprox.CylLocInt.Cover

/-!
# Leaf `T12/1/3/1/a`: local integrability of a periodic `L^r` field

Proves `cylLocInt : CylLocInt` (SP 1923-1926). A `c`-periodic field in `L^r(avgμ c)`, `1 < r`,
is `L^r` on the cell (`memLp_cell_of_avg`); it is then `L^1` on every closed ball, since the
ball is covered by finitely many translates of the cell (`lintegral_closedBall_le`) and the
`L^r` norm on a finite-measure set controls the `L^1` norm (`MemLp.integrable`).
Helpers live in `CylLocInt/Cover.lean`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb

theorem cylLocInt : UnforcedLeray.Short.IIb.CylLocInt := by
  intro c r hc hr D hD
  have hper : UnforcedLeray.Cyl.IsPeriodic c D := hD.1
  have hmem : MemLp D (ENNReal.ofReal r) (UnforcedLeray.Cyl.cellμ c) :=
    CylLocIntCover.memLp_cell_of_avg hc hD.2
  intro x
  exact ⟨Metric.closedBall x 1, Metric.closedBall_mem_nhds x one_pos,
    CylLocIntCover.integrableOn_closedBall_of_cell hc hr.le hper hmem x 1⟩

end UnforcedLeray.Short.IIb
