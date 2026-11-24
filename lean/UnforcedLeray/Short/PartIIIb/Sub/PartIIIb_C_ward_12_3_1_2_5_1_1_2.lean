import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GEQuadSub.GEQMem.Ddu
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.rawSmoothBdd_Sub.Lemmas

/-!
# `InletFnMeas` from the joint smoothness of `raw`

Source `the November 2 reference manuscript`
lines 2563-2569, 1206-1222: the inlet `E_i` and `raw` are `C^∞` jointly in `(τ,y)`
(`inlet_contDiff_joint` for `ν ≤ 1`; `RawJointSmooth` is the source fact on `raw`, tracked as task
`PartIII-b:C/ward/12/3/1/2/6/1/1`).  Hence `inletFn = -∂_j(L₀E_i + (raw·∇)E_i + (E_i·∇)raw)` is
continuous, hence a.e. strongly measurable.
-/

set_option autoImplicit false

noncomputable section

open UnforcedLeray.PhaseSpace MeasureTheory Set
open scoped ContDiff
open UnforcedLeray.Cons.C03.Concrete (Params advT)

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem contDiff_realC_meas : ContDiff ℝ ∞ (fun x : UnforcedLeray.Space => UnforcedLeray.B0412.realC x) := by
  apply (contDiff_piLp 2).2
  intro i
  have hcoord : (fun x : UnforcedLeray.Space => (UnforcedLeray.B0412.realC x).ofLp i) =
      fun x : UnforcedLeray.Space => ((x i : ℝ) : ℂ) := by
    funext x
    exact UnforcedLeray.B0412.realC_apply x i
  rw [hcoord]
  exact Complex.ofRealCLM.contDiff.comp
    (contDiff_piLp_apply (p := 2) (i := i))

theorem fderiv_slice_meas {R : ℝ × UnforcedLeray.Space → UnforcedLeray.Space}
    (hR : Differentiable ℝ R) (τ : ℝ) (y v : UnforcedLeray.Space) :
    fderiv ℝ (fun x : UnforcedLeray.Space => R (τ, x)) y v = fderiv ℝ R (τ, y) (0, v) := by
  have hmap : HasFDerivAt (fun x : UnforcedLeray.Space => (τ, x))
      ((0 : UnforcedLeray.Space →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ UnforcedLeray.Space)) y :=
    (hasFDerivAt_const τ y).prodMk (hasFDerivAt_id y)
  have hcomp := (hR (τ, y)).hasFDerivAt.comp y hmap
  have h := congrArg (fun A : UnforcedLeray.Space →L[ℝ] UnforcedLeray.Space => A v) hcomp.fderiv
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply,
    zero_apply] using h

theorem inletSrc_contDiff {p : Params} {i : Fin 2}
    (hE : ContDiff ℝ ∞ (p.Efun i))
    (hR : ContDiff ℝ ∞ (fun x : ℝ × UnforcedLeray.Space => p.raw x.1 x.2)) :
    ContDiff ℝ ∞ (inletSrc p i) := by
  have hL : ContDiff ℝ ∞ (UnforcedLeray.B0411.L0 p.ν (p.Efun i)) := by
    unfold UnforcedLeray.B0411.L0 UnforcedLeray.B0411.T0
    exact (((contDiff_dτ hE).sub ((contDiff_radialT hE).const_smul _)).sub
      ((contDiff_lapT hE).const_smul _)).sub (hE.const_smul _)
  have hU : ContDiff ℝ ∞ (fun x : ℝ × UnforcedLeray.Space =>
      UnforcedLeray.B0412.realC (p.raw x.1 x.2)) := contDiff_realC_meas.comp hR
  have hA : ContDiff ℝ ∞ (advT (fun x => UnforcedLeray.B0412.realC (p.raw x.1 x.2)) (p.Efun i)) := by
    unfold advT
    exact ContDiff.sum fun k _ =>
      ((contDiff_piLp_apply (p := 2) (i := k)).comp hU).smul (UnforcedLeray.PhaseSpace.contDiff_dy hE k)
  have hG : ContDiff ℝ ∞ (gradAlong p.raw (p.Efun i)) := by
    unfold gradAlong
    apply (contDiff_piLp 2).2
    intro l
    show ContDiff ℝ ∞ (fun x : ℝ × UnforcedLeray.Space => ∑ k : Fin 3, p.Efun i x k *
      ((fderiv ℝ (p.raw x.1) x.2 (EuclideanSpace.single k 1) l : ℝ) : ℂ))
    refine ContDiff.sum fun k _ => ?_
    have h1 : ContDiff ℝ ∞ (fun x : ℝ × UnforcedLeray.Space => p.Efun i x k) :=
      (contDiff_piLp_apply (p := 2) (i := k)).comp hE
    have h2 : ContDiff ℝ ∞ (fun x : ℝ × UnforcedLeray.Space =>
        fderiv ℝ (p.raw x.1) x.2 (EuclideanSpace.single k 1) l) := by
      have h3 : ContDiff ℝ ∞ (fun x : ℝ × UnforcedLeray.Space =>
          fderiv ℝ (fun w : ℝ × UnforcedLeray.Space => p.raw w.1 w.2) x (0, EuclideanSpace.single k 1)) :=
        (hR.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
      have h4 := (contDiff_piLp_apply (p := 2) (i := l)).comp h3
      have heq : (fun x : ℝ × UnforcedLeray.Space =>
          fderiv ℝ (p.raw x.1) x.2 (EuclideanSpace.single k 1) l) = fun x =>
          (fderiv ℝ (fun w : ℝ × UnforcedLeray.Space => p.raw w.1 w.2) x
            (0, EuclideanSpace.single k 1)) l := by
        funext x
        have := fderiv_slice_meas (R := fun w : ℝ × UnforcedLeray.Space => p.raw w.1 w.2)
          (hR.differentiable (by simp)) x.1 x.2 (EuclideanSpace.single k 1)
        exact congrArg (fun v => v l) this
      rw [heq]
      exact h4
    exact h1.mul (Complex.ofRealCLM.contDiff.comp h2)
  exact (hL.add hA).add hG

theorem inletFnMeas_of (hraw : RawJointSmooth) : InletFnMeas := by
  intro lam q hq dm dp hdm
  obtain ⟨ν1, hν1, H⟩ := hraw dm dp hdm
  refine ⟨min ν1 1, lt_min hν1 one_pos, fun p d hreg hν hm z g hg i j => ?_⟩
  have hR := H p d hreg (hν.trans (min_le_left _ _))
  have hI := inlet_contDiff_joint lam q hq hreg (hν.trans (min_le_right _ _)) hm i
  have hE : ContDiff ℝ ∞ (p.Efun i) := contDiff_realC_meas.comp hI
  have hF : ContDiff ℝ ∞ (inletFn p i j) := (UnforcedLeray.PhaseSpace.contDiff_dy (inletSrc_contDiff hE hR) j).neg
  exact hF.continuous.aestronglyMeasurable

end UnforcedLeray.Short.PartIIIb.Concrete
