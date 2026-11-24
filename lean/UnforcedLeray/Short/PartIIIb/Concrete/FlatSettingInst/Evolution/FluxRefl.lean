import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Evolution.Leaves

/-!
# The train flux intertwines the reflections (source 287-288, 2819-2836)

Source of record: `the November 2 reference manuscript` (73 pages).

`B(r)ω = vω + E K_cω` with `v` odd (source 287-288) and `E = curl v` even (`ec_even`):
`B(r)(ω(-·)) = -(B(r)ω)(-·)` (`fluxBOnRefl_of`, from `StripVelRefl`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Evol

open UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution
open UnforcedLeray.Short.IIIa.Exist (vortFn fluxFn cplx stripVel)

/-- **`FluxBOnRefl`** from `StripVelRefl` (source 287-288: the train is odd). -/
theorem fluxBOnRefl_of (hV : StripVelRefl) : FluxBOnRefl := by
  intro ν c m _ hm tr T hT P r w
  set s : ℝ := (actualTrainAgeClamp T hT r).1 with hs_def
  have hs : 0 ≤ s := (actualTrainAgeClamp T hT r).2.1
  have e : actualTrainFluxBOn hm P r = physicalFluxKernelCLM hm (UnforcedLeray.B0238.Vc tr s)
      (UnforcedLeray.B0238.Ec tr s) (continuous_actualTrainVelocity_slice tr hs)
      (continuous_actualTrainCurl_slice tr hs) P.hCv P.hCE
      (P.velocity_bound (actualTrainAgeClamp T hT r))
      (P.weighted_curl_bound (actualTrainAgeClamp T hT r)) := rfl
  rw [e]
  funext i
  refine Lp.ext (ae_cellMeasure_of_ae_cell ?_)
  have hB := UnforcedLeray.Short.IIIa.Exist.L4Aux.fluxFn_ae hm (UnforcedLeray.B0238.Vc tr s)
    (UnforcedLeray.B0238.Ec tr s) (continuous_actualTrainVelocity_slice tr hs)
    (continuous_actualTrainCurl_slice tr hs) P.hCv P.hCE
    (P.velocity_bound (actualTrainAgeClamp T hT r))
    (P.weighted_curl_bound (actualTrainAgeClamp T hT r)) w i
  have hBR := UnforcedLeray.Short.IIIa.Exist.L4Aux.fluxFn_ae hm (UnforcedLeray.B0238.Vc tr s)
    (UnforcedLeray.B0238.Ec tr s) (continuous_actualTrainVelocity_slice tr hs)
    (continuous_actualTrainCurl_slice tr hs) P.hCv P.hCE
    (P.velocity_bound (actualTrainAgeClamp T hT r))
    (P.weighted_curl_bound (actualTrainAgeClamp T hT r)) (reflV hm w) i
  have hBneg := (mp_neg_cell c).quasiMeasurePreserving.ae hB
  filter_upwards [hBR, hBneg, fluxFn_reflF (physicalFluxKernelCLM hm (UnforcedLeray.B0238.Vc tr s)
      (UnforcedLeray.B0238.Ec tr s) (continuous_actualTrainVelocity_slice tr hs)
      (continuous_actualTrainCurl_slice tr hs) P.hCv P.hCE
      (P.velocity_bound (actualTrainAgeClamp T hT r))
      (P.weighted_curl_bound (actualTrainAgeClamp T hT r)) w) i,
    vortFn_reflV hm w, hV c m hm w] with x h1 h2 h3 h4 h5
  change fluxFn _ i x = fluxFn (reflF _) i x
  rw [h1, h3, h2]
  simp only [vortFn] at h4
  rw [h4]
  have h5' := h5 i
  simp only [stripVel] at h5'
  have h6 : ((UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.realBiotSavart hm
      (reflV hm w).1 ((mem_zeroCirculationSubmodule_iff (by linarith) (reflV hm w).1).1
        (reflV hm w).2) x : UnforcedLeray.Train.Vec) i) =
      -((UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution.realBiotSavart hm w.1
        ((mem_zeroCirculationSubmodule_iff (by linarith) w.1).1 w.2) (-x) :
          UnforcedLeray.Train.Vec) i) := by
    exact_mod_cast h5'
  rw [h6]
  have hodd : UnforcedLeray.B0238.Vc tr s (-x) i = -UnforcedLeray.B0238.Vc tr s x i := by
    simp only [UnforcedLeray.B0238.Vc]
    rw [tr.isTrain.odd s hs x]
    rfl
  rw [hodd, ec_even tr hs x]
  ring

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Evol
