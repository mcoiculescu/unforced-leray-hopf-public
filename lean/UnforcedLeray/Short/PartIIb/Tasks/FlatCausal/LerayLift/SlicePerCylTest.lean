import UnforcedLeray.Short.PartIIb.Sub.T12_2_5

/-!
# Part II-b, task `PartII-b:T12/2/5/1`: the periodized test is a cell test

Source of record: `the November 2 reference manuscript` (SP 1923-1926). Proves the Prop
`SlicePerCylTest` of `Sub/T12_2_5.lean` by the periodization lemmas of
`Tasks/HilbertEnergy/ProductRule/PeriodizeCellTest.lean`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb.LerayLiftSub

theorem slicePerCylTest_proof : UnforcedLeray.Short.IIb.LerayLiftSub.SlicePerCylTest := by
  intro c φ hc hφ hcs s
  obtain ⟨R, hR⟩ := pcell_bound_gen hcs (fun y : Coord => y.2.1) (by fun_prop)
  obtain ⟨T, hT⟩ := pcell_bound_gen hcs (fun y : Coord => y.1) (by fun_prop)
  obtain ⟨L, hL⟩ := pcell_bound_gen hcs (fun y : Coord => y.2.2) (by fun_prop)
  refine ⟨?_, ?_, ?_⟩
  · exact (pcellPer_contDiff hφ hc hR).comp (contDiff_const.prodMk contDiff_id)
  · intro z
    exact pcellPer_periodic c (s, z)
  · refine ⟨L, fun z hz => ?_⟩
    exact pcellPer_compact (c := c) hT hL (s, z) (Or.inr hz)

end UnforcedLeray.Short.IIb.LerayLiftSub
