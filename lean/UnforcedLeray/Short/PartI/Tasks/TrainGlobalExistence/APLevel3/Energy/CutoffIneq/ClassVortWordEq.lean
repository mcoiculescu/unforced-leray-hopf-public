import UnforcedLeray.Short.PartI.Sub.PartI_T04_10_1_2_1
import UnforcedLeray.Short.PartI.Sub.PartI_T08_1
import UnforcedLeray.Short.PartI.Sub.PartI_T08_2_2.EnergyIneq
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APLevel3.Energy.CutoffIneq.SliceWordTimeCommOn
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APLevel2.CutCont
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APEllipticC
import UnforcedLeray.Short.PartI.Tasks.VorticityFirstMoment.LocalVorticityEquation
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.ErrJetL2.VelocityJetL2.EnergyIneq.VortWordEquation
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.ErrJetL2.VelocityJetL2.EnergyIneq.DerivWordLapComm

/-!
# Part I, `PartI:T04/10/1/2/1/5`: `ClassVortWordEq`

Source of record: `the November 2 reference manuscript`, lines 286-288
(the scalar vorticity equation).  The differentiated vorticity equation for the words `∂_u ω`
of a class solution, `s ∈ (0,T)`.

Route (as `vortWordEquation_proof`): the pointwise equation `∂_s ω = νΔω - v·∇ω` from
`localVorticityEquation`; `SliceWordTimeCommOn` moves `∂_s` inside the word; linearity of the word
on smooth fields; `DerivWordLapComm` commutes the word past the Laplacian.
-/

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Cyl (Plane)

/-- **Target** `classVortWordEq_proof`: the differentiated scalar vorticity equation for the
words of a class solution (`ClassVortWordEq`, `Sub/PartI_T04_10_1_2_1.lean`). -/
theorem classVortWordEq_proof : ClassVortWordEq := by
  intro ν c T v p hν hc hcls s hs u z
  have hv : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => v x.1 x.2) (Icc 0 T ×ˢ (univ : Set Plane)) :=
    hcls.classical.smooth_v
  have hF : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => Cyl.curl (v x.1) x.2)
      (Ioo 0 T ×ˢ (univ : Set Plane)) :=
    (apcc_curl_smooth hcls.pos hv).mono (prod_mono Ioo_subset_Icc_self subset_rfl)
  -- `∂_s` commutes with the spatial word
  have hcomm : deriv (fun t => B0151.derivWord u (Cyl.curl (v t)) z) s =
      B0151.derivWord u (fun z' => deriv (fun t => Cyl.curl (v t) z') s) z :=
    (sliceWordTimeCommOn_proof 0 T _ hF u).2 s hs z
  -- the scalar vorticity equation, pointwise in `z`
  have hpt : ∀ z' : Plane, deriv (fun t => Cyl.curl (v t) z') s =
      ν * Train.lapS (Cyl.curl (v s)) z' - scalarAdv (v s) (Cyl.curl (v s)) z' := by
    intro z'
    have h := localVorticityEquation ν c T v p hν hc hcls.pos hcls.classical s hs z'
    unfold UnforcedLeray.B0238.vorticityResidual at h
    unfold scalarAdv
    linarith
  have e2 : B0151.derivWord u (fun z' => deriv (fun t => Cyl.curl (v t) z') s) z =
      B0151.derivWord u (fun z' => ν * Train.lapS (Cyl.curl (v s)) z' -
        scalarAdv (v s) (Cyl.curl (v s)) z') z :=
    congrArg (fun g => B0151.derivWord u g z) (funext hpt)
  -- smoothness of the slice and its curl
  have hsm : ContDiff ℝ ∞ (v s) := IsClassicalOn.contDiff_slice hcls.classical
    (Ioo_subset_Icc_self hs)
  have hω : ContDiff ℝ ∞ (Cyl.curl (v s)) := APEllipticCaux.curl_contDiff hsm
  have hA : ContDiff ℝ ∞ (Train.lapS (Cyl.curl (v s))) := vjl_lapS_contDiff hω
  have hG : ContDiff ℝ ∞ (scalarAdv (v s) (Cyl.curl (v s))) :=
    vjl_scalarAdv_contDiff hsm hω
  -- linearity of the word
  have k1 : B0151.derivWord u (fun x => ν * Train.lapS (Cyl.curl (v s)) x -
      scalarAdv (v s) (Cyl.curl (v s)) x) z =
      B0151.derivWord u (fun x => ν * Train.lapS (Cyl.curl (v s)) x) z -
        B0151.derivWord u (scalarAdv (v s) (Cyl.curl (v s))) z :=
    derivWord_sub_smooth
      (show ContDiff ℝ ∞ (fun x => ν * Train.lapS (Cyl.curl (v s)) x) from
        contDiff_const.mul hA) hG u z
  have k2 : B0151.derivWord u (fun x => ν * Train.lapS (Cyl.curl (v s)) x) z =
      ν * B0151.derivWord u (Train.lapS (Cyl.curl (v s))) z :=
    vwDerivWord_const_mul ν u (Train.lapS (Cyl.curl (v s))) hA z
  have k3 : B0151.derivWord u (Train.lapS (Cyl.curl (v s))) =
      Train.lapS (B0151.derivWord u (Cyl.curl (v s))) :=
    derivWordLapComm_proof (Cyl.curl (v s)) hω u
  have k3z : B0151.derivWord u (Train.lapS (Cyl.curl (v s))) z =
      Train.lapS (B0151.derivWord u (Cyl.curl (v s))) z :=
    congrFun k3 z
  rw [hcomm, e2, k1, k2, k3z]

end UnforcedLeray.Short.PartI
