import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_pins_4_2

/-!
# `SpaceIBPPairing` (task `PartIII-b:C/near/pins/4/2/2`)

Integration by parts on `ℝ³` for a `C¹` complex `g` and a compactly supported `C¹` real `f`,
from Mathlib's `integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable` with `𝕜 = ℂ`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.NearInst

open MeasureTheory

/-- The complex-valued real-direction derivative of a real function, cast to `ℂ`. -/
theorem ofRealComp_fderiv_spaceIBP {f : Space → ℝ} (hf : ContDiff ℝ 1 f) (y v : Space) :
    fderiv ℝ (fun x => ((f x : ℝ) : ℂ)) y v = ((fderiv ℝ f y v : ℝ) : ℂ) := by
  have hd : DifferentiableAt ℝ f y := (hf.differentiable (by norm_num)) y
  have h1 : HasFDerivAt (fun x => ((f x : ℝ) : ℂ))
      (Complex.ofRealCLM.comp (fderiv ℝ f y)) y :=
    HasFDerivAt.comp y (Complex.ofRealCLM.hasFDerivAt) hd.hasFDerivAt
  rw [h1.fderiv]
  simp

set_option maxHeartbeats 1000000 in
theorem spaceIBPPairing : SpaceIBPPairing := by
  unfold SpaceIBPPairing
  intro f g hf hfc hg j
  have hGc : HasCompactSupport (fun y => ((f y : ℝ) : ℂ)) :=
    HasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) hfc (by simp)
  have hGd : ContDiff ℝ 1 (fun y => ((f y : ℝ) : ℂ)) := Complex.ofRealCLM.contDiff.comp hf
  have hGcont : Continuous (fun y => ((f y : ℝ) : ℂ)) := hGd.continuous
  have hgd : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hGdiff : Differentiable ℝ (fun y => ((f y : ℝ) : ℂ)) := hGd.differentiable (by norm_num)
  have hgder : Continuous (fderiv ℝ g) := hg.continuous_fderiv (by norm_num)
  have hgcont : Continuous g := hg.continuous
  have hD : HasCompactSupport (fderiv ℝ (fun y => ((f y : ℝ) : ℂ))) :=
    HasCompactSupport.fderiv (𝕜 := ℝ) hGc
  have hI1 : MeasureTheory.Integrable (fun x => fderiv ℝ g x (coordinateVector j) *
      ((f x : ℝ) : ℂ)) := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact (hgder.clm_apply continuous_const).mul hGcont
    · exact hGc.mul_left
  have hI2 : MeasureTheory.Integrable (fun x => g x *
      fderiv ℝ (fun y => ((f y : ℝ) : ℂ)) x (coordinateVector j)) := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact hgcont.mul ((hGd.continuous_fderiv (by norm_num)).clm_apply continuous_const)
    · exact (hD.comp_left (g := fun L : Space →L[ℝ] ℂ => L (coordinateVector j))
        (by simp)).mul_left
  have hI3 : MeasureTheory.Integrable (fun x => g x * ((f x : ℝ) : ℂ)) := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact hgcont.mul hGcont
    · exact hGc.mul_left
  have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := g) (g := fun y => ((f y : ℝ) : ℂ)) (v := coordinateVector j)
    hI1 hI2 hI3 (fun x _ => hgd x) (fun x _ => hGdiff x)
  simp only [ofRealComp_fderiv_spaceIBP hf] at key
  exact key

end UnforcedLeray.Short.PartIIIb.NearInst
