import UnforcedLeray.Short.PartIIb.Sub.T12_2_3
import UnforcedLeray.Short.PartIIb.Tasks.FlatCausal.LerayLift.SliceCylLpAe
import UnforcedLeray.Lib.BochnerTime.Slices

/-!
# Sub-lemma `T12/2/3/1` (`SliceClassPath`): the class path of the slices is strongly measurable

Source of record: `the November 2 reference manuscript`, lines 1923-1926.
Target: `UnforcedLeray.Short.IIb.LerayLiftSub.SliceClassPath` (`Sub/T12_2_3.lean`).

Proof: take `u := BochnerTime.toPathLq (ofReal r) (avgμ c) F'`, the slice path `s ↦ [F'(s,·)]` (equal to
the class of the slice whenever the slice is in `L^r`, and `0` otherwise). Strong measurability of `u`
is `BochnerTime.stronglyMeasurable_toPathLq`. For a.e. `s > 0` the slice is `CylLp` by
`SliceCylLpAe`, so `toPathLq_of_memLp` and `MemLp.coeFn_toLp` identify `u s` with the slice.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb

theorem sliceClassPath_proof : UnforcedLeray.Short.IIb.LerayLiftSub.SliceClassPath := by
  intro c r hc hr F' hF hper hfin
  have := LerayLiftSub.fact_one_le_ofReal hr
  haveI : Fact (ENNReal.ofReal r ≠ ⊤) := ⟨ENNReal.ofReal_ne_top⟩
  haveI : SFinite (UnforcedLeray.Cyl.avgμ c) := by
    unfold UnforcedLeray.Cyl.avgμ UnforcedLeray.Cyl.cellμ
    infer_instance
  refine ⟨UnforcedLeray.BochnerTime.toPathLq (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c) F', ?_, ?_⟩
  · exact UnforcedLeray.BochnerTime.stronglyMeasurable_toPathLq hF
  · filter_upwards [sliceCylLpAe_proof c r hc hr F' hF hper hfin] with s hs
    have hmem : MemLp (fun z => F' (s, z)) (ENNReal.ofReal r) (UnforcedLeray.Cyl.avgμ c) := hs.2
    rw [UnforcedLeray.BochnerTime.toPathLq_of_memLp hmem]
    exact MemLp.coeFn_toLp hmem

end UnforcedLeray.Short.IIb
