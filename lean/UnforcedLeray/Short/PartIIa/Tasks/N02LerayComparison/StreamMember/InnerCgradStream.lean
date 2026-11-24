import UnforcedLeray.Short.PartIIa.Sub.N02_2
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.StreamMember.Identity

/-!


Source of record: `the November 2 reference manuscript`, lines 1730-1732.

`Φc`) and `C^∞` `ψ`, `⟪cgrad ε Φ p, streamC ε ψ p⟫` is the divergence-term combination of
`integrand_identity`: `cgrad` is real, `(Deps ε Φ p : ℂ) = pdQ Φc p - ε opK Φc p` and
`(Axi.dEta Φ p : ℂ) = pdEta Φc p` (chain rule through `Complex.ofRealCLM`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226
open NearStreamMemberAux

/-- The derivative of the complexification of a real `C^∞` function is the complexification of the
derivative. -/
theorem icsFderivOfReal {Φ : Profile → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (p v : Profile) :
    fderiv ℝ (fun x => (Φ x : ℂ)) p v = ((fderiv ℝ Φ p v : ℝ) : ℂ) := by
  have hd : DifferentiableAt ℝ Φ p := (hΦ.differentiable (by simp)) p
  have h : HasFDerivAt (fun x => (Φ x : ℂ)) (Complex.ofRealCLM.comp (fderiv ℝ Φ p)) p :=
    Complex.ofRealCLM.hasFDerivAt.comp p hd.hasFDerivAt
  rw [h.fderiv]
  simp

/---/
theorem innerCgradStream : InnerCgradStream := by
  intro ε c Φ Φc hΦc ψ hψ p
  have hfun : Φc = fun x => (Φ.1 x : ℂ) := funext hΦc
  subst hfun
  have hΦ : ContDiff ℝ ∞ Φ.1 := Φ.2.smooth
  have hΦC : ContDiff ℝ ∞ (fun x => (Φ.1 x : ℂ)) := Complex.ofRealCLM.contDiff.comp hΦ
  rw [← integrand_identity ε hΦC hψ p]
  have hq : pdQ (fun x => (Φ.1 x : ℂ)) p = ((Axi.dQ Φ.1 p : ℝ) : ℂ) := icsFderivOfReal hΦ p _
  have hs : pdS (fun x => (Φ.1 x : ℂ)) p = ((Axi.dS Φ.1 p : ℝ) : ℂ) := icsFderivOfReal hΦ p _
  have he : pdEta (fun x => (Φ.1 x : ℂ)) p = ((Axi.dEta Φ.1 p : ℝ) : ℂ) :=
    icsFderivOfReal hΦ p _
  have hK : opK (fun x => (Φ.1 x : ℂ)) p = ((Kop Φ.1 p : ℝ) : ℂ) := by
    rw [opK_eq, hs, he]
    simp [Kop]
    ring
  simp only [cgrad, streamC, PiLp.inner_apply, Fin.sum_univ_two, Deps]
  rw [hq, hK, he]
  simp
  ring

end UnforcedLeray.Short.PartIIa
