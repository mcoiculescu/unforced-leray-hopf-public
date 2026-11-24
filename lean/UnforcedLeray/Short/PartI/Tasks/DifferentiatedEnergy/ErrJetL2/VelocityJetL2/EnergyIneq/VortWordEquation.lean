import UnforcedLeray.Short.PartI.Sub.PartI_T08_2_2.EnergyIneq
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.ErrJetL2.VelocityJetL2.EnergyIneq.SliceWordReg
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.ErrJetL2.VelocityJetL2.EnergyIneq.SliceWordTimeComm
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.ErrJetL2.VelocityJetL2.EnergyIneq.DerivWordLapComm
import UnforcedLeray.Units.B0238.VorticityEq

/-!
# Part I, task `PartI:T08/2/2/2/4` (`VortWordEquation`): the differentiated vorticity equation

Source of record: `the November 2 reference manuscript`, lines 276-288 (scalar
vorticity equation, line 286).

Route: `B0238.vorticityResidual_eq_zero` gives `∂_s ω(z) = ν Δω(z) - (v·∇ω)(z)` pointwise in `z`
for `s > 0`; `SliceWordTimeComm` moves `∂_s` inside the spatial word `u`; `derivWord` is linear
on smooth functions (`derivWord_sub_smooth` and `vwDerivWord_const_mul`), and
`DerivWordLapComm` commutes the word past the Laplacian.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec)

/-- Scalar multiples pass through a spatial word on smooth functions. -/
theorem vwDerivWord_const_mul (c : ℝ) :
    ∀ (w : List Bool) (f : Plane → ℝ), ContDiff ℝ ∞ f → ∀ z : Plane,
      B0151.derivWord w (fun x => c * f x) z = c * B0151.derivWord w f z
  | [], _, _, _ => rfl
  | true :: w, f, hf, z => by
      have h1 := B0151.contDiff_derivWord hf w
      have e : B0151.derivWord w (fun x => c * f x) = fun x => c * B0151.derivWord w f x :=
        funext (vwDerivWord_const_mul c w f hf)
      have hd : Differentiable ℝ (B0151.derivWord w f) := h1.differentiable (by simp)
      show GaussianVortex.partialX (B0151.derivWord w (fun x => c * f x)) z =
        c * GaussianVortex.partialX (B0151.derivWord w f) z
      rw [e, B0151.partialX_eq_fderiv (hd.const_mul c), fderiv_const_mul (hd z) c,
        B0151.partialX_eq_fderiv hd]
      rfl
  | false :: w, f, hf, z => by
      have h1 := B0151.contDiff_derivWord hf w
      have e : B0151.derivWord w (fun x => c * f x) = fun x => c * B0151.derivWord w f x :=
        funext (vwDerivWord_const_mul c w f hf)
      have hd : Differentiable ℝ (B0151.derivWord w f) := h1.differentiable (by simp)
      show GaussianVortex.partialY (B0151.derivWord w (fun x => c * f x)) z =
        c * GaussianVortex.partialY (B0151.derivWord w f) z
      rw [e, B0151.partialY_eq_fderiv (hd.const_mul c), fderiv_const_mul (hd z) c,
        B0151.partialY_eq_fderiv hd]
      rfl

theorem vortWordEquation_proof : UnforcedLeray.Short.PartI.VortWordEquation := by
  intro ν c _hν _hc tr s hs u z
  have hω : ContDiff ℝ ∞ (Cyl.curl (tr.v s)) := vjl_vortWord_contDiff tr hs.le []
  -- the scalar vorticity equation, pointwise in `z`
  have hpt : ∀ z' : Plane, deriv (fun t => Cyl.curl (tr.v t) z') s =
      ν * Train.lapS (Cyl.curl (tr.v s)) z' - scalarAdv (tr.v s) (Cyl.curl (tr.v s)) z' := by
    intro z'
    have h := UnforcedLeray.B0238.vorticityResidual_eq_zero (u := tr.v) (p := tr.p)
      tr.isTrain.smooth_v tr.isTrain.smooth_p
      (fun r hr z'' => tr.isTrain.solenoidal r hr.le z'') tr.isTrain.momentum hs z'
    unfold UnforcedLeray.B0238.vorticityResidual at h
    unfold scalarAdv
    linarith
  -- the space-time vorticity is `C^∞` on `(0, ∞) × ℝ²`
  have hF : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => Cyl.curl (tr.v x.1) x.2) (Ioi 0 ×ˢ univ) :=
    (vjl_vortWord_joint sliceWordReg_proof tr []).mono
      (prod_mono Ioi_subset_Ici_self subset_rfl)
  -- `∂_s` commutes with the spatial word
  have hcomm' := sliceWordTimeComm_proof (fun x : ℝ × Plane => Cyl.curl (tr.v x.1) x.2) hF u s z hs
  have e2 : B0151.derivWord u (fun z' => deriv (fun t => Cyl.curl (tr.v t) z') s) z =
      B0151.derivWord u (fun z' => ν * Train.lapS (Cyl.curl (tr.v s)) z' -
        scalarAdv (tr.v s) (Cyl.curl (tr.v s)) z') z :=
    congrArg (fun g => B0151.derivWord u g z) (funext hpt)
  have hcomm2 : deriv (fun t => vortWord tr u t z) s =
      B0151.derivWord u (fun z' => ν * Train.lapS (Cyl.curl (tr.v s)) z' -
        scalarAdv (tr.v s) (Cyl.curl (tr.v s)) z') z :=
    hcomm'.trans e2
  -- linearity of the word on smooth functions
  have hA : ContDiff ℝ ∞ (Train.lapS (Cyl.curl (tr.v s))) := vjl_lapS_contDiff hω
  have hb : ContDiff ℝ ∞ (tr.v s) :=
    TrainErrorEquation.contDiff_slice (f := tr.v) tr.isTrain.smooth_v hs.le
  have hG : ContDiff ℝ ∞ (scalarAdv (tr.v s) (Cyl.curl (tr.v s))) :=
    vjl_scalarAdv_contDiff hb hω
  have k1 : B0151.derivWord u (fun x => ν * Train.lapS (Cyl.curl (tr.v s)) x -
      scalarAdv (tr.v s) (Cyl.curl (tr.v s)) x) z =
      B0151.derivWord u (fun x => ν * Train.lapS (Cyl.curl (tr.v s)) x) z -
        B0151.derivWord u (scalarAdv (tr.v s) (Cyl.curl (tr.v s))) z :=
    derivWord_sub_smooth
      (show ContDiff ℝ ∞ (fun x => ν * Train.lapS (Cyl.curl (tr.v s)) x) from
        contDiff_const.mul hA) hG u z
  have k2 : B0151.derivWord u (fun x => ν * Train.lapS (Cyl.curl (tr.v s)) x) z =
      ν * B0151.derivWord u (Train.lapS (Cyl.curl (tr.v s))) z :=
    vwDerivWord_const_mul ν u (Train.lapS (Cyl.curl (tr.v s))) hA z
  have k3 : B0151.derivWord u (Train.lapS (Cyl.curl (tr.v s))) =
      Train.lapS (vortWord tr u s) :=
    derivWordLapComm_proof (Cyl.curl (tr.v s)) hω u
  rw [hcomm2, k1, k2, k3]

end UnforcedLeray.Short.PartI
