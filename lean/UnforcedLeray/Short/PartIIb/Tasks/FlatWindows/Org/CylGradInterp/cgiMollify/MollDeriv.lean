import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T13_1_5_5

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology

/-- The complexification `κ ↦ (κ : ℂ)` of a real kernel, as a function on `Coord`. -/
def mollDerivG (κ : Coord → ℝ) : Coord → ℂ := fun z => (κ z : ℂ)

theorem mollDeriv_conv_eq (κ : Coord → ℝ) (f : Coord → ℂ) :
    convK κ f = MeasureTheory.convolution f (mollDerivG κ) (ContinuousLinearMap.mul ℝ ℂ) volume := by
  funext x
  simp [convK, MeasureTheory.convolution, mollDerivG]

theorem mollDeriv_fderiv_g (κ : Coord → ℝ) (hκ : ContDiff ℝ ∞ κ) (z : Coord) :
    fderiv ℝ (mollDerivG κ) z = (Complex.ofRealCLM).comp (fderiv ℝ κ z) := by
  have hdiff : Differentiable ℝ κ := hκ.differentiable (by simp)
  have h1 : HasFDerivAt κ (fderiv ℝ κ z) z := (hdiff z).hasFDerivAt
  have h2 := (Complex.ofRealCLM.hasFDerivAt).comp z h1
  exact h2.fderiv

theorem mollDeriv_proof : UnforcedLeray.Short.IIb.MollDeriv := by
  intro κ f hκ hf j
  obtain ⟨hκs, hκc⟩ := hκ
  have hκ1 : ContDiff ℝ 1 κ := hκs.of_le (by simp)
  have hg : ContDiff ℝ 1 (mollDerivG κ) := Complex.ofRealCLM.contDiff.comp hκ1
  have hcg : HasCompactSupport (mollDerivG κ) := hκc.comp_left Complex.ofReal_zero
  have hd := fun x => hcg.hasFDerivAt_convolution_right (𝕜 := ℝ)
    (L := ContinuousLinearMap.mul ℝ ℂ) (μ := volume) hf hg x
  have hcont : Continuous (fderiv ℝ (mollDerivG κ)) := hg.continuous_fderiv (by simp)
  have hex : ConvolutionExists f (fderiv ℝ (mollDerivG κ))
      ((ContinuousLinearMap.mul ℝ ℂ).precompR Coord) volume :=
    HasCompactSupport.convolutionExists_right ((ContinuousLinearMap.mul ℝ ℂ).precompR Coord)
      (HasCompactSupport.fderiv (𝕜 := ℝ) hcg) hf hcont
  funext x
  unfold cdv
  rw [mollDeriv_conv_eq κ f, (hd x).fderiv]
  show (∫ t, ((ContinuousLinearMap.mul ℝ ℂ).precompR Coord) (f t)
      (fderiv ℝ (mollDerivG κ) (x - t)) ∂volume) (cdir j) = convK (cpd j κ) f x
  rw [ContinuousLinearMap.integral_apply (hex x)]
  unfold convK
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp [cpd, mollDeriv_fderiv_g κ hκs]

end UnforcedLeray.Short.IIb
