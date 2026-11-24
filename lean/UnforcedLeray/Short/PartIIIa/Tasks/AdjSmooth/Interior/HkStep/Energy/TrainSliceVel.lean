import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.HkStep.Energy.TrainSliceVel.Bridge

/-!
# `PartIII-a:T21/2/7/2/1/1/5/18/3`: the slices of the train velocity

Source of record: `the November 2 reference manuscript` (SP), lines 270-288,
2866-2870.  From the joint derivative bounds `TrainSTJets` on `[0, S]`, each slice `v(r)`,
`r ∈ [0, S]`, is smooth, `c`-periodic, divergence free, with uniform derivative bounds
(`Bridge.lean`: the slice derivative is the within derivative of the space-time field, exactly).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

theorem trainSliceVel : UnforcedLeray.Short.IIIa.TrainSliceVel := by
  intro ν c tr m S hS hJ
  unfold TrainSTJets at hJ
  choose C hC using hJ
  have hF : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2)
      (Ici (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := tr.isTrain.smooth_v
  refine ⟨fun i => C i, fun r hr => ?_⟩
  unfold SliceVel
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact slice_contDiff (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2) hF hr.1
  · exact tr.isTrain.periodic_v r hr.1
  · intro z
    exact tr.isTrain.solenoidal r hr.1 z
  · intro i x
    exact le_trans (slice_iteratedFDeriv_le (fun p : ℝ × (ℝ × ℝ) => tr.v p.1 p.2) hF hr.1 i x)
      (hC i r hr x).1

end UnforcedLeray.Short.IIIa
