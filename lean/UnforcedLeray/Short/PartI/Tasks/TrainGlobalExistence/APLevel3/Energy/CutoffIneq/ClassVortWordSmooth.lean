import UnforcedLeray.Short.PartI.Sub.PartI_T04_10_1_2_1
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APLevel3.Energy.CutoffIneq.SliceWordTimeCommOn
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APLevel2.CutCont

/-!
# Part I, `PartI:T04/10/1/2/1/3`: `ClassVortWordSmooth`

Source of record: `the November 2 reference manuscript`, lines 276-288.
Smoothness of the vorticity words `∂_u ω` on the open strip `(0,T) × ℝ²`.
-/

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Cyl (Plane)

/-- **Target** `classVortWordSmooth_proof`: smoothness of the vorticity words on `(0,T) × ℝ²`
(`ClassVortWordSmooth`, `Sub/PartI_T04_10_1_2_1.lean`). -/
theorem classVortWordSmooth_proof : ClassVortWordSmooth := by
  intro ν c T v p hν hc hcls u
  have hv : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => v x.1 x.2) (Icc 0 T ×ˢ (univ : Set Plane)) :=
    hcls.classical.smooth_v
  have hF : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => Cyl.curl (v x.1) x.2)
      (Ioo 0 T ×ˢ (univ : Set Plane)) :=
    (apcc_curl_smooth hcls.pos hv).mono (prod_mono Ioo_subset_Icc_self subset_rfl)
  exact (sliceWordTimeCommOn_proof 0 T _ hF u).1

end UnforcedLeray.Short.PartI
