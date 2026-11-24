import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_2
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Sub.IIIb_D2_3_2_8_5

/-!
# `PartIII-b:C/ward/12/3/1/2/5/1/2/6`: `inletPairSplit_of`

Source `the November 2 reference manuscript`
lines 2385-2387.
-/

set_option autoImplicit false

noncomputable section

open UnforcedLeray.PhaseSpace MeasureTheory Set
open scoped ContDiff
open UnforcedLeray.Cons.C03.Concrete (Params IsSolTest pairF convT advT rep)

namespace UnforcedLeray.Short.PartIIIb.Concrete

private theorem contDiff_raw_of_realC' {p : Params}
    (hRC : ContDiff ℝ ∞ (fun x : ℝ × UnforcedLeray.Space =>
      UnforcedLeray.B0412.realC (p.raw x.1 x.2))) :
    ContDiff ℝ ∞ (fun x : ℝ × UnforcedLeray.Space => p.raw x.1 x.2) := by
  apply (contDiff_piLp 2).2
  intro k
  have hcoord : (fun x : ℝ × UnforcedLeray.Space => (p.raw x.1 x.2).ofLp k) =
      fun x : ℝ × UnforcedLeray.Space => (UnforcedLeray.B0412.realC (p.raw x.1 x.2) k).re := by
    funext x
    simp [UnforcedLeray.B0412.realC_apply]
  rw [hcoord]
  exact Complex.reCLM.contDiff.comp ((contDiff_piLp_apply (p := 2) (i := k)).comp hRC)

private theorem contDiff_inletSrc_parts {p : Params} {i : Fin 2}
    (hE : ContDiff ℝ ∞ (p.Efun i))
    (hU : ContDiff ℝ ∞ (fun x : ℝ × UnforcedLeray.Space =>
      UnforcedLeray.B0412.realC (p.raw x.1 x.2))) :
    ContDiff ℝ ∞ (UnforcedLeray.B0411.L0 p.ν (p.Efun i)) ∧
    ContDiff ℝ ∞ (advT (fun x => UnforcedLeray.B0412.realC (p.raw x.1 x.2)) (p.Efun i)) ∧
    ContDiff ℝ ∞ (gradAlong p.raw (p.Efun i)) := by
  have hR := contDiff_raw_of_realC' hU
  have hL : ContDiff ℝ ∞ (UnforcedLeray.B0411.L0 p.ν (p.Efun i)) := by
    unfold UnforcedLeray.B0411.L0 UnforcedLeray.B0411.T0
    exact (((contDiff_dτ hE).sub ((contDiff_radialT hE).const_smul _)).sub
      ((contDiff_lapT hE).const_smul _)).sub (hE.const_smul _)
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
  exact ⟨hL, hA, hG⟩

theorem inletPairSplit_of (hReg : InletFieldRegular) : InletPairSplit := by
  intro lam q hq dm dp hdm
  obtain ⟨ν₀, hν₀, H0⟩ := hReg lam q hq dm dp hdm
  refine ⟨ν₀, hν₀, fun p d hreg hν hm z g hg i ψ hψ => ?_⟩
  obtain ⟨hRC, _, hE⟩ := H0 p d hreg hν hm z g hg
  obtain ⟨hL, hA, hG⟩ := contDiff_inletSrc_parts (hE i).1 hRC
  have cL := hL.continuous
  have cA := hA.continuous
  have cG := hG.continuous
  unfold inletSrc
  have e1 := (ibpLin_proved p.period ψ hψ _ _ (cL.add cA) cG).1
  have e2 := (ibpLin_proved p.period ψ hψ _ _ cL cA).1
  exact e1.trans (congrArg (· + pairF p.period ψ (gradAlong p.raw (p.Efun i))) e2)

end UnforcedLeray.Short.PartIIIb.Concrete
