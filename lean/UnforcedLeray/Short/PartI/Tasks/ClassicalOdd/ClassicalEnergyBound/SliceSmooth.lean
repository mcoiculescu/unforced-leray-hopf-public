import UnforcedLeray.Short.PartI.Sub.T02_3_10

/-!
# Part I, task `PartI:T02/3/10`: `ebSliceSmooth` (toolkit leaf)

Source of record: `the November 2 reference manuscript`, lines 276-282 (the classical
solution on each finite interval, used by the cutoff energy method).
Target: `EbSliceSmooth` (`Short/PartI/Sub/T02_3_10.lean`, line 107).

Route. For `s ∈ [0, T]` the map `z ↦ (s, z)` is smooth and sends `univ` into `Icc 0 T ×ˢ univ`.
Composing the joint smoothness of `hcl.smooth_v` and `hcl.smooth_p` on `Icc 0 T ×ˢ univ` with this map
gives smoothness of the slices `v s` and `p s` on the whole plane. This is the argument of
`trainSliceSmooth` (`Tasks/TrainCutoffEnergyProof/SliceSmooth.lean`), with `Icc 0 T` in place of `Ici 0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec)

/-- The slices `v(s)` and `p(s)` of a classical solution on `[0, T]` are `C^∞` on the plane, for
`s ∈ [0, T]`. -/
theorem ebSliceSmooth : EbSliceSmooth := by
  intro ν c T v p hcl s hs
  have h2 : ContDiff ℝ ∞ (fun z : Plane => ((s, z) : ℝ × Plane)) :=
    contDiff_const.prodMk contDiff_id
  have hv := hcl.smooth_v.comp (h2.contDiffOn (s := (Set.univ : Set Plane)))
    (fun z _ => Set.mk_mem_prod hs (Set.mem_univ z))
  have hp := hcl.smooth_p.comp (h2.contDiffOn (s := (Set.univ : Set Plane)))
    (fun z _ => Set.mk_mem_prod hs (Set.mem_univ z))
  exact ⟨contDiffOn_univ.1 hv, contDiffOn_univ.1 hp⟩

end UnforcedLeray.Short.PartI
