import UnforcedLeray.Short.PartIIb.Sub.T12_2_3
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.LerayLift.SlicePeriodicRep

/-!
# Sub-lemma `T12/2/3/3` (`AvgRedQId`): `avgμ` is carried by the cell, where `redQ` is the identity

Source of record: `the November 2 reference manuscript`, lines 1923-1926.
Target: `UnforcedLeray.Short.IIb.LerayLiftSub.AvgRedQId` (`Sub/T12_2_3.lean`).

Proof: `avgμ c = ofReal c⁻¹ • cellμ c` and `cellμ c = volume.restrict (cell c)`, so the a.e. statement
reduces (via `ae_smul_measure_eq` and `ae_restrict_iff'`) to the membership `z.1 ∈ Ico (-c/2) (c/2)`,
where `redQ_of_mem_cell` gives `redQ c z.1 = z.1`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb

theorem avgRedQId_proof : UnforcedLeray.Short.IIb.LerayLiftSub.AvgRedQId := by
  intro c hc
  have hcpos : ENNReal.ofReal c⁻¹ ≠ 0 := (ENNReal.ofReal_pos.2 (inv_pos.2 hc)).ne'
  unfold UnforcedLeray.Cyl.avgμ UnforcedLeray.Cyl.cellμ UnforcedLeray.Cyl.cell
  rw [Measure.ae_ennreal_smul_measure_eq hcpos,
    ae_restrict_iff' (measurableSet_Ico.prod MeasurableSet.univ)]
  refine ae_of_all _ fun z hz => ?_
  have hq : z.1 ∈ Ico (-c / 2) (c / 2) := hz.1
  rw [UnforcedLeray.Short.IIb.LerayLiftSub.redQ_of_mem_cell hc hq]

end UnforcedLeray.Short.IIb
