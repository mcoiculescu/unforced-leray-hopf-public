import UnforcedLeray.Short.PartI.Sub.T02_3_11

/-!
# Part I, task `PartI:T02/3/11`: `CcSliceSmooth` (toolkit leaf)

Source of record: `the November 2 reference manuscript`, lines 276-288 (energy
method: transverse cutoff, difference of two classical solutions).
Target: `CcSliceSmooth` (`Short/PartI/Sub/T02_3_11.lean`, line 151).

Route. For `s ∈ [0, T]` the map `z ↦ (s, z)` is smooth and sends `univ` into
`Icc 0 T ×ˢ univ`. Composing the joint smoothness of `v` and `p` on `Icc 0 T ×ˢ univ`
(`IsClassicalOn.smooth_v`, `IsClassicalOn.smooth_p`) with this map gives smoothness of the
slices `v s` and `p s` on the whole plane. The train analogue is `trainSliceSmooth`
(`Tasks/TrainCutoffEnergyProof/SliceSmooth.lean`), with `Ici 0` in place of `Icc 0 T`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)

/-- **`PartI:T02/3/11`, auxiliary `CcSliceSmooth`**: for `s ∈ [0, T]` the slices `v(s)` and `p(s)`
of a classical solution are `C^∞` on the plane. -/
theorem ccSliceSmooth : CcSliceSmooth := by
  intro ν c T v p hcl s hs
  have h2 : ContDiff ℝ ∞ (fun z : Plane => ((s, z) : ℝ × Plane)) :=
    contDiff_const.prodMk contDiff_id
  have hv := hcl.smooth_v.comp (h2.contDiffOn (s := (Set.univ : Set Plane)))
    (fun z _ => ⟨hs, Set.mem_univ z⟩)
  have hp := hcl.smooth_p.comp (h2.contDiffOn (s := (Set.univ : Set Plane)))
    (fun z _ => ⟨hs, Set.mem_univ z⟩)
  exact ⟨contDiffOn_univ.1 hv, contDiffOn_univ.1 hp⟩

end UnforcedLeray.Short.PartI
