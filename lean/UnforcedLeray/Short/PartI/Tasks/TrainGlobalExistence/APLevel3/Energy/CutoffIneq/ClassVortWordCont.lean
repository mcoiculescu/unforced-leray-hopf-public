import UnforcedLeray.Short.PartI.Sub.PartI_T04_10_1_2_1
import UnforcedLeray.Short.PartI.Tasks.CylinderInterpolation.JetWord
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APLevel2.CutCont
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APEllipticC

/-!
# Part I, `PartI:T04/10/1/2/1/4`: `ClassVortWordCont`

Source of record: `the November 2 reference manuscript`, lines 276-288.
Continuity of the vorticity words `∂_u ω` on the closed strip `[0,T] × ℝ²`.
-/

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Cyl (Plane)

/-- **Target** `classVortWordCont_proof`: continuity of the vorticity words on `[0,T] × ℝ²`
(`ClassVortWordCont`, `Sub/PartI_T04_10_1_2_1.lean`). -/
theorem classVortWordCont_proof : ClassVortWordCont := by
  intro ν c T v p hν hc hcls u
  have hv : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => v x.1 x.2) (Icc 0 T ×ˢ (univ : Set Plane)) :=
    hcls.classical.smooth_v
  have hGs := apcc_curl_smooth hcls.pos hv
  have hJ := apcc_jet_joint hcls.pos hGs u.length
  have hE : ContinuousOn
      (fun x : ℝ × Plane => iteratedFDeriv ℝ u.length (Cyl.curl (v x.1)) x.2
        (fun i => cjwE (u.get i))) (Icc 0 T ×ˢ (univ : Set Plane)) := by
    have hap : Continuous (fun M : ContinuousMultilinearMap ℝ (fun _ : Fin u.length => Plane) ℝ =>
        M (fun i => cjwE (u.get i))) :=
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin u.length => Plane) ℝ
        (fun i => cjwE (u.get i))).continuous
    exact hap.comp_continuousOn hJ
  refine hE.congr (fun x hx => ?_)
  have hsm : ContDiff ℝ ∞ (v x.1) := IsClassicalOn.contDiff_slice hcls.classical hx.1
  have hcurl : ContDiff ℝ ∞ (Cyl.curl (v x.1)) := APEllipticCaux.curl_contDiff hsm
  have e := cjw_word_formula (Cyl.curl (v x.1)) hcurl u.length u.get x.2
  rw [List.ofFn_get] at e
  exact e

end UnforcedLeray.Short.PartI
