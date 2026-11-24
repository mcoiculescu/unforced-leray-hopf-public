import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_3.Defs

/-!
# `PartIII-b:C/rep/8/3/2/6`: smoothness of the train slices (source 2141-2161)

For `s ≥ 0` the flat profiles `v(s, ·)` and `p_cyl(s, ·)` of a train are `C²`, resp.
differentiable, from `IsTrain.smooth_v` and `IsTrain.smooth_p` (smooth on `[0,∞) × ℝ²`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The velocity `v(s, ·)` of a train is `C^∞` on `ℝ²` for `s ≥ 0`. -/
theorem ts_velocity_slice (L : ReturnLevel) (s : ℝ) (hs : 0 ≤ s) :
    ContDiff ℝ ∞ (fun y : ℝ × ℝ => L.train.v s y) := by
  have hv := L.train.isTrain.smooth_v
  have hg : ContDiff ℝ ∞ (fun y : ℝ × ℝ => ((s, y) : ℝ × (ℝ × ℝ))) :=
    contDiff_const.prodMk contDiff_id
  have hmaps : MapsTo (fun y : ℝ × ℝ => ((s, y) : ℝ × (ℝ × ℝ))) univ (Ici 0 ×ˢ univ) :=
    fun y _ => ⟨hs, mem_univ y⟩
  have hcomp := hv.comp hg.contDiffOn hmaps
  exact contDiffOn_univ.mp hcomp

/-- The pressure `p(s, ·)` of a train is `C^∞` on `ℝ²` for `s ≥ 0`. -/
theorem ts_pressure_slice (L : ReturnLevel) (s : ℝ) (hs : 0 ≤ s) :
    ContDiff ℝ ∞ (fun y : ℝ × ℝ => L.train.p s y) := by
  have hp := L.train.isTrain.smooth_p
  have hg : ContDiff ℝ ∞ (fun y : ℝ × ℝ => ((s, y) : ℝ × (ℝ × ℝ))) :=
    contDiff_const.prodMk contDiff_id
  have hmaps : MapsTo (fun y : ℝ × ℝ => ((s, y) : ℝ × (ℝ × ℝ))) univ (Ici 0 ×ˢ univ) :=
    fun y _ => ⟨hs, mem_univ y⟩
  have hcomp := hp.comp hg.contDiffOn hmaps
  exact contDiffOn_univ.mp hcomp

/-- **The train slices are smooth** (`TrainSliceSmooth`, source 2141-2161). -/
theorem trainSliceSmooth : TrainSliceSmooth := by
  intro L s hs
  refine ⟨?_, ?_⟩
  · have h0 : ContDiff ℝ ∞ (fun y : ℝ × ℝ => L.train.v s y 0) :=
      (EuclideanSpace.proj (0 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp
        (ts_velocity_slice L s hs)
    have h1 : ContDiff ℝ ∞ (fun y : ℝ × ℝ => L.train.v s y 1) :=
      (EuclideanSpace.proj (1 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp
        (ts_velocity_slice L s hs)
    exact (h0.prodMk h1).of_le (by simp)
  · exact (ts_pressure_slice L s hs).differentiable (by simp)

end UnforcedLeray.Short.PartIIIb.Concrete
