import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_1_3
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# First-order operators with affine `η`-coefficients and their jets
(`PartIII-b:C/rep/8/2/1/3/b`, helper 1)

Source lines 5036-5045, 5464-5465.  In the dilation variable `z = (σ, (q, η))` the ring-chart
profile operators are `Gop a b c d e F = a ∂_q F + b ∂_σ F + (c + dη) ∂_η F + e F`.  The jet sum
`J n F z = Σ_{k ≤ n} ‖D^k F z‖` and the one-step estimate
`J n (Gop … F) z ≤ (|a|+|b|+|c|+|d|(|η|+n)+|e|) J (n+1) F z`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.RingFrameD2BoundAux

abbrev Zc : Type := ℝ × (ℝ × ℝ)

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `a ∂_q F + b ∂_σ F + (c + d η) ∂_η F + e F`. -/
def Gop (a b c d e : ℝ) (F : Zc → E) : Zc → E := fun z =>
  a • fderiv ℝ F z (0, (1, 0)) + b • fderiv ℝ F z (1, (0, 0)) +
    (c + d * z.2.2) • fderiv ℝ F z (0, (0, 1)) + e • F z

theorem contDiff_Gop (a b c d e : ℝ) {F : Zc → E} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (Gop a b c d e F) := by
  have h1 : ContDiff ℝ ∞ (fderiv ℝ F) := hF.fderiv_right (by simp)
  have hq : ContDiff ℝ ∞ (fun z => fderiv ℝ F z ((0 : ℝ), ((1 : ℝ), (0 : ℝ)))) :=
    h1.clm_apply contDiff_const
  have hs : ContDiff ℝ ∞ (fun z => fderiv ℝ F z ((1 : ℝ), ((0 : ℝ), (0 : ℝ)))) :=
    h1.clm_apply contDiff_const
  have he : ContDiff ℝ ∞ (fun z => fderiv ℝ F z ((0 : ℝ), ((0 : ℝ), (1 : ℝ)))) :=
    h1.clm_apply contDiff_const
  have hη : ContDiff ℝ ∞ (fun z : Zc => z.2.2) := contDiff_snd.comp contDiff_snd
  unfold Gop
  exact (((contDiff_const.smul hq).add (contDiff_const.smul hs)).add
    ((contDiff_const.add (contDiff_const.mul hη)).smul he)).add (contDiff_const.smul hF)

theorem Gop_add_smul (a b c d e : ℝ) {F G : Zc → E} (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    (t : ℝ) :
    Gop a b c d e (fun z => F z + t • G z) = fun z => Gop a b c d e F z + t • Gop a b c d e G z := by
  funext z
  have hFd : DifferentiableAt ℝ F z := (hF.differentiable (by simp)) z
  have hGd : DifferentiableAt ℝ G z := (hG.differentiable (by simp)) z
  have h : fderiv ℝ (fun z => F z + t • G z) z = fderiv ℝ F z + t • fderiv ℝ G z := by
    exact (hFd.hasFDerivAt.add (hGd.hasFDerivAt.const_smul t)).fderiv
  simp only [Gop, h, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]
  module

theorem Gop_sub (a b c d e : ℝ) {F G : Zc → E} (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) :
    Gop a b c d e (fun z => F z - G z) = fun z => Gop a b c d e F z - Gop a b c d e G z := by
  funext z
  have hFd : DifferentiableAt ℝ F z := (hF.differentiable (by simp)) z
  have hGd : DifferentiableAt ℝ G z := (hG.differentiable (by simp)) z
  have h : fderiv ℝ (fun z => F z - G z) z = fderiv ℝ F z - fderiv ℝ G z :=
    (hFd.hasFDerivAt.sub hGd.hasFDerivAt).fderiv
  simp only [Gop, h, ContinuousLinearMap.sub_apply]
  module

theorem Gop_neg (a b c d e : ℝ) {F : Zc → E} (hF : ContDiff ℝ ∞ F) :
    Gop a b c d e (fun z => -F z) = fun z => -Gop a b c d e F z := by
  funext z
  have hFd : DifferentiableAt ℝ F z := (hF.differentiable (by simp)) z
  have h : fderiv ℝ (fun z => -F z) z = -fderiv ℝ F z := hFd.hasFDerivAt.neg.fderiv
  simp only [Gop, h, ContinuousLinearMap.neg_apply]
  module

theorem Gop_params (a b c d e a' b' c' d' e' : ℝ) (F : Zc → E) (z : Zc) :
    Gop a b c d e F z - Gop a' b' c' d' e' F z = Gop (a - a') (b - b') (c - c') (d - d') (e - e') F z := by
  simp only [Gop]
  module

end

end UnforcedLeray.Short.PartIIIb.Concrete.RingFrameD2BoundAux
