import UnforcedLeray.Short.PartI.Sub.T05b_2

/-!
# Part I, task `PartI:T05b/2/2`: `TrainSliceSmooth` (toolkit leaf)

Source of record: `the November 2 reference manuscript`, lines 261-288.
Target: `TrainSliceSmooth` (`Short/PartI/Sub/T05b_2.lean`, line 152).

Route. For `s ≥ 0` the map `z ↦ (s, z)` is smooth and sends `univ` into `Ici 0 ×ˢ univ`.
Composing the joint smoothness of `tr.v` and `tr.p` on `Ici 0 ×ˢ univ` with this map gives
smoothness of the slices `tr.v s` and `tr.p s` on the whole plane. The same argument is used in
`Short/PartI/Sub/T02_5.lean` (`streamExists_of`), with `Icc 0 T` in place of `Ici 0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)

/-- The slices `v(s)` and `p(s)` of a train are `C^∞` on the plane, for `s ≥ 0`. -/
theorem trainSliceSmooth : TrainSliceSmooth := by
  intro ν c tr s hs
  have h2 : ContDiff ℝ ∞ (fun z : Plane => ((s, z) : ℝ × Plane)) :=
    contDiff_const.prodMk contDiff_id
  have hv := tr.isTrain.smooth_v.comp (h2.contDiffOn (s := (Set.univ : Set Plane)))
    (fun z _ => ⟨Set.mem_Ici.2 hs, Set.mem_univ z⟩)
  have hp := tr.isTrain.smooth_p.comp (h2.contDiffOn (s := (Set.univ : Set Plane)))
    (fun z _ => ⟨Set.mem_Ici.2 hs, Set.mem_univ z⟩)
  exact ⟨contDiffOn_univ.1 hv, contDiffOn_univ.1 hp⟩

end UnforcedLeray.Short.PartI
